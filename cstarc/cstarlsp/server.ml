open Core
open Async
open Lsp.Types
open ExtProtocol


let dispatch_request :
    type a. a Lsp.Client_request.t -> (a, string) result Deferred.t =
  function
  | Initialize _ -> failwith "Unexpected initialize request"
  | TextDocumentHover params -> Action.handle_hover params
  | Shutdown -> Action.handle_shutdown ()
  | _ -> failwith "Not implemented"

let dispatch_std_notification =
  let open Lsp.Client_notification in
  function
  | TextDocumentDidOpen params -> Action.on_document_open params
  | TextDocumentDidChange params -> Action.on_document_change params
  | TextDocumentDidClose params -> Action.on_document_close params
  | DidSaveTextDocument params -> Action.on_document_save params
  | ChangeConfiguration params -> eprintf "[CStar LSP] Receive ChangeConfiguration Notification\n" ; Action.on_workspaceDidChangeConfiguration params
  | _ -> return ()

let dispatch_notification =
  let open ExtProtocol.Notification.Client_ in
  function
  | ShowSym params -> eprintf "[CStar LSP] Receive ShowSym Notification\n" ; Action.on_sym_show params
  (* | ShowSymFile params -> eprintf "[CStar LSP] Receive ShowSymFile Notification\n" ; Action.on_symfile_show params *)
  | Std notif -> dispatch_std_notification notif

let parse_packet buf =
  Yojson.Safe.from_string buf |> Jsonrpc.Packet.t_of_yojson

let dump_response packet =
  Jsonrpc.Response.yojson_of_t packet |> Yojson.Safe.to_string

let dump_notification notif = 
  Notification.Server_.to_jsonrpc notif |> Jsonrpc.Notification.yojson_of_t |> Yojson.Safe.to_string

let handle_notification channel notif = 
  eprintf "[CStar LSP] handle_notification\n";
  Stdio.write channel (dump_notification notif)

(* reference:
   - https://github.com/maximedenes/jasmin-language-server
   - https://docs.rs/lsp-server/
*)

let handle_message channel buf =
  let open Jsonrpc.Packet in
  match parse_packet buf with
  | Request req -> (
    match Lsp.Client_request.of_jsonrpc req with
    | Error _ ->
        eprintf "Failed to parse request: %s\n" buf ;
        return ()
    | Ok (E request) ->
        let%bind resp = dispatch_request request in
        let resp =
          match resp with
          | Ok resp ->
              Lsp.Client_request.yojson_of_result request resp
              |> Jsonrpc.Response.ok req.id
          | Error e -> Errors.request_failed req.id e
        in
        Stdio.write channel (dump_response resp) )
  | Response _res -> return () (* unknown response *)
  | Notification noti -> (
    match Notification.Client_.of_jsonrpc noti with
    | Ok notification -> dispatch_notification notification
    | Error _ -> return @@ eprintf "Failed to parse notification: %s\n" buf )
  | _ -> failwith "Not implemented"

let rec initialize_start channel =
  let%bind msg = Stdio.read channel in
  let msg = Option.value_exn msg ~message:"Failed to read from channel" in
  match parse_packet msg with
  | Request req -> (
    match Lsp.Client_request.of_jsonrpc req with
    | Error _ -> failwith (Format.sprintf "Failed to parse request: %s" msg)
    | Ok (E request) -> (
      match request with
      | Initialize params -> return (req.id, params)
      | _ ->
          let resp =
            Errors.server_not_initialized req.id
              (Format.sprintf "expected initialize request, got %s" msg)
            |> dump_response
          in
          let%bind () = Stdio.write channel resp in
          initialize_start channel ) )
  | Response _res -> failwith "Unexpected response"
  | Notification notif -> (
    match Lsp.Client_notification.of_jsonrpc notif with
    | Error _ -> failwith "Failed to parse notification"
    | Ok notif -> (
      match notif with
      | Lsp.Client_notification.Exit -> failwith "Unexpected exit"
      | _ -> initialize_start channel ) )
  | _ -> failwith "Not implemented"

let initialize_finish channel id result =
  let result = InitializeResult.yojson_of_t result in
  let resp = Jsonrpc.Response.ok id result in
  let%bind () = Stdio.write channel (resp |> dump_response) in
  let%bind msg = Stdio.read channel in
  let msg = Option.value_exn msg ~message:"Failed to read from channel" in
  match parse_packet msg with
  | Request _req -> failwith "Unexpected request"
  | Response _res -> failwith "Unexpected response"
  | Notification notif -> (
    match Lsp.Client_notification.of_jsonrpc notif with
    | Error _ -> failwith "Failed to parse notification"
    | Ok notif -> (
      match notif with
      | Lsp.Client_notification.Initialized -> return ()
      | _ -> failwith "Unexpected notification" ) )
  | _ -> failwith "Not implemented"

let initialize channel =
  eprintf "[CStar LSP] Initializing\n" ;
  let%bind id, params = initialize_start channel in

  let InitializeParams.{ initializationOptions ; _ } = params in
  begin match initializationOptions with
  | None -> failwith "Failed to get initialization options"
  | Some initializationOptions ->
    Action.do_configuration @@ Settings.t_of_yojson initializationOptions;
  end;

  eprintf "[CStar LSP] Initialize params: %s\n"
    (InitializeParams.yojson_of_t params |> Yojson.Safe.to_string) ;
  
  let result =
    InitializeResult.create ~capabilities:Action.capabilities ()
  in
  let finish = initialize_finish channel id result in
  eprintf "[CStar LSP] Initialized\n" ;
  finish

let run channel =
  let%bind () = initialize channel in
  let finished_recerive = ref false in
  let finished_send = ref false in
  while%bind return ((not !finished_recerive) || (not !finished_send)) do
    (* receive *)
    let%bind _ = 
      match%bind Stdio.read channel with
      | Some msg -> handle_message channel msg
      | None -> return (finished_recerive := true)
    in
    (* send *)
    match Queue.dequeue NotifQueue.q with
    | Some notif -> handle_notification channel notif
    | None -> return (finished_send := true)
  done
