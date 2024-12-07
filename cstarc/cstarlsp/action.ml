open Core
open Async
open Lsp.Types
open Settings
open ExtProtocol

let capabilities =
  ServerCapabilities.create ~hoverProvider:(`Bool true)
    ~textDocumentSync:(`TextDocumentSyncKind TextDocumentSyncKind.Full) ()

let serverroot = ref {HolLitePath.path = ""}

let bdwgcflag = ref {BDWGCFlag.flags = ""}

let do_configuration settings = 
  serverroot := settings.hollitepath ;
  bdwgcflag := settings.bdwgcflag

let get_filename_without_extension path =
  let basename = Filename.basename path in
  let remove_extension name =
    match String.rindex name '.' with
    | None -> name
    | Some index -> String.sub name ~pos:0 ~len:index
  in
  remove_extension basename

module LexCache = struct
  open Async
  (* module DocMap = Stdlib.Map.Make (String) *)

  let from_pos (pos : Lexing.position) =
    Position.create ~line:(pos.pos_lnum - 1)
      ~character:(pos.pos_cnum - pos.pos_bol)

  let contains (range : Range.t) ~(pos : Position.t) =
    let start = range.start in
    let end_ = range.end_ in
    start.line <= pos.line && pos.line <= end_.line
    && (start.line <> pos.line || start.character <= pos.character)
    && (end_.line <> pos.line || pos.character <= end_.character)

  (* let cache : Range.t list Map.t ref = ref Map.empty (module String) *)
  let cache = ref (Map.empty (module String))

  let update uri =
    let key = DocumentUri.to_string uri in
    let%map file = Reader.file_contents @@ DocumentUri.to_path uri in
    (* Lex the file; TODO: parse and dump *)
    let lexbuf = Lexing.from_string file in
    let rec lex () =
      match Cstarparse.Lexer.lexer lexbuf with
      | Cstarparse.Parser.EOF -> []
      | _ ->
          let token =
            Range.create
              ~start:(lexbuf.lex_start_p |> from_pos)
              ~end_:(lexbuf.lex_curr_p |> from_pos)
          in
          token :: lex ()
    in
    cache := Map.set !cache ~key:key ~data:(lex ())

  let get uri = Map.find !cache (DocumentUri.to_string uri) 

  let lookup ranges pos =
    match List.find ranges ~f:(contains ~pos) with
    | Some range -> range
    | None -> List.hd_exn ranges
end

let get_log_file cstpath = !serverroot.path ^ "cstar_output/"^ (get_filename_without_extension cstpath) ^"_log.csv"

let in_range ~line ~col ~range =
  let open Lsp.Types.Range in
  if line < range.start.line || line > range.end_.line then false
  else if line = range.start.line && col < range.start.character then false
  else if line = range.end_.line && col > range.end_.character then false
  else true

let get_file_modification_time file =
  let open Caml_unix in
  try
    let { st_mtime; _ } = stat file in
    st_mtime
  with Unix_error(ENOENT, _, _) ->
    time ()
  | Unix_error(err, _, _) ->
    failwith ("Error: " ^ (error_message err) ^"\n")

let format_time time_ =
  let open Caml_unix in
  let tm = gmtime time_ in
  Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02d"
    (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday
    tm.tm_hour tm.tm_min tm.tm_sec

let file_exists filename =
  match%bind Sys.file_exists filename with
  | `Yes -> return true
  | _ -> return false

let parse_csv_data data =
  let csv = Csv.of_string ~separator:'@' data in
  Csv.input_all csv
  
let handle_hover (params : HoverParams.t) :
    (Hover.t option, string) result Deferred.t =
  match params.textDocument.uri |> LexCache.get with
  | None ->
      return @@ Error "cannot find the thm for hovering, try save the file!"
  | Some ranges -> (
      let range = params.position |> LexCache.lookup ranges in
      eprintf "[CStar LSP] Hovering (%d, %d)..(%d, %d)\n" range.start.line
        range.start.character range.end_.line range.end_.character ;
      match%bind (file_exists (get_log_file (DocumentUri.to_path params.textDocument.uri))) with
      | false -> return @@ Ok None
      | true -> (
        let%bind log_content = Reader.file_contents (get_log_file (DocumentUri.to_path params.textDocument.uri)) in
        let log = parse_csv_data log_content in
        let rec find_log log =
          match log with
          | [] -> Ok None
          | (line :: col :: thm :: _) :: rest ->
              let line = int_of_string line in
              let col = int_of_string col in
              eprintf "[CStar LSP] Hovering (%d, %d)!!!\n" line col;
              if in_range ~line ~col ~range then Ok (Some thm)
              else find_log rest
          | _ -> Error "malformed log file"
        in
        match find_log log with
        | Ok (Some thm) ->
            let contents =
              `MarkupContent
                (MarkupContent.create ~kind:MarkupKind.PlainText ~value:thm)
            in
            let hover = Hover.create ~contents ~range () in
            return @@ Ok (Some hover)
        | Ok None -> return @@ Ok None
        | Error e -> return @@ Error e ))

(* let handle_hover (params : HoverParams.t) :
    (Hover.t option, string) result Deferred.t =
  match params.textDocument.uri |> LexCache.get with
  | None ->
      return @@ Error "cannot find the thm for hovering, try save the file!"
  | Some ranges -> (
      let range = params.position |> LexCache.lookup ranges in
      eprintf "[CStar LSP] Hovering (%d, %d)...(%d, %d)\n" range.start.line
        range.start.character range.end_.line range.end_.character ;
      match%bind (file_exists (get_log_file (DocumentUri.to_path params.textDocument.uri))) with
      | false -> return @@ Ok None
      | true -> (
        let%bind log = Reader.file_contents (get_log_file (DocumentUri.to_path params.textDocument.uri)) in
        (* eprintf "[CStar LSP] Opening log %s!!!\n" @@ log; *)
        let log = Csv.of_string log ~separator:'@' in
        (* eprintf "[CStar LSP] Opening log %s!!!\n" @@ List.hd_exn (Csv.next log); *)
        let rec find_log () =
          try
            match Csv.next log with
            | line :: col :: thm :: _ ->
                let line = int_of_string line in
                let col = int_of_string col in
                eprintf "[CStar LSP] %d!!!\n" line;
                if in_range ~line ~col ~range then Ok (Some thm)
                else find_log ()
            | _ -> Error "malformed log file"
          with
          | End_of_file -> Ok None (* Not found in log *)
          | _ -> Error "malformed log file"
        in
        match find_log () with
        | Ok (Some thm) ->
            let contents =
              `MarkupContent
                (MarkupContent.create ~kind:MarkupKind.PlainText ~value:thm)
            in
            let hover = Hover.create ~contents ~range () in
            return @@ Ok (Some hover)
        | Ok None -> return @@ Ok None
        | Error e -> return @@ Error e )) *)

let handle_shutdown () : (unit, string) result Deferred.t = return @@ Ok ()

let on_document_open (params : DidOpenTextDocumentParams.t) = LexCache.update params.textDocument.uri

let on_document_close (_params : DidCloseTextDocumentParams.t) = return ()

let on_document_change (_params : DidChangeTextDocumentParams.t) = return () 

let on_document_save (params : DidSaveTextDocumentParams.t) = 
  (* send file_time notification before changed *)
  let open ExtProtocol.Notification.Server_ in
  let filepath_ = DocumentUri.to_path params.textDocument.uri in
  let lasttime = (get_log_file filepath_) |> get_file_modification_time |> format_time in
  Queue.enqueue NotifQueue.q (HoverfileResult {HoverfileResultParams.filepath = (get_log_file filepath_); HoverfileResultParams.lasttime});
  (* generate .csv *)
  let filepath = DocumentUri.to_path params.textDocument.uri in 
  let filename = get_filename_without_extension filepath in
  let command = 
    "cd " ^ !serverroot.path ^ " && mkdir cstar_output > /dev/null 2>&1"
    ^ " ; ./cstarc/_build/default/main.exe " ^ filepath ^" -output cstar_output/" ^ filename ^ ".output.c > /dev/null 2>&1"
    ^ " && cd " ^ !serverroot.path ^ " && clang -o cstar_output/" ^ filename ^ "_log cstar_output/"^ filename ^".output.c -I./lcf_server/includes -O3 -L./lcf_server/proof-user -L./lcf_server/target/release "^ !bdwgcflag.flags ^" -lproof_conv -lproof_user -lproof_kernel -lm -std=c2x"
    ^ " && cd " ^ !serverroot.path ^ " && ./cstar_output/" ^ filename ^ "_log > /dev/null 2>&1" in
  let _ = Unix.system command in ();
  (* update cache *)
  LexCache.update params.textDocument.uri

let get_context_before_linenum filepath linenum =
  let%map file_content = Reader.file_contents filepath in
  let lines = String.split_lines file_content in
  let context_lines = List.take lines (linenum - 1) in
  String.concat ~sep:"\n" context_lines

let on_sym_show (params : Notification.Client_.ShowSymParams.t) = 
  (* TODO: get ghostline by VST-A *)
  let open ExtProtocol.Notification.Server_ in
  let filepath = params.filepath in
  let filename = get_filename_without_extension filepath in
  let linenum = params.line in 
  (* let%bind context = get_context_before_linenum params.filepath linenum in *)
  let command = 
    "cd " ^ !serverroot.path ^ " && gcc ./cstar_output/"^ filename ^".c -o ./cstar_output/"^ filename ^"_sym -L./sac_c_parser/test/build -lsac -Wl,-rpath ./sac_c_parser/test/build > /dev/null 2>&1" 
    ^ " && ./cstar_output/" ^ filename ^ "_sym > ./cstar_output/"^ filename ^".msg 2>&1" in
  let%bind _ = Process.run ~prog:"sh" ~args:["-c"; command] () in
  let%bind msg_content = Reader.file_contents (!serverroot.path ^ "cstar_output/"^ filename ^".msg") in
  let ghostlines = String.split_lines msg_content in
  Queue.enqueue NotifQueue.q (SymResult {SymResultParams.linenum; SymResultParams.ghostlines});
  return () 

(* let remove_substring_from_start str sub =
  let len_sub = String.length sub in
  if String.length str < len_sub then str
  else if String.equal (String.sub str ~pos:0 ~len:len_sub) sub then
    (String.sub str ~pos:len_sub ~len:(String.length str - len_sub))
  else
    str

let on_symfile_show (params : Notification.Client_.ShowSymFileParams.t) = 
  (* TODO: get ghostline by VST-A *)
  let open ExtProtocol.Notification.Server_ in
  let filepath = params.filepath in
  let filename = get_filename_without_extension filepath in
  let filepath_docker = remove_substring_from_start filepath !serverroot.path in
  let tmpfile = !serverroot.path ^ "cstar_output/" ^ filename ^ ".vst" in 
  let outfile = !serverroot.path ^ "cstar_output/" ^ filename ^ ".output" in 
  let command = 
    "cd " ^ !serverroot.path ^ "cstarc" ^ " && mkdir ../cstar_output > /dev/null 2>&1"
    ^ " ; dune exec -- " ^ "./cstarc.exe " ^ filepath ^" -vst " ^ tmpfile ^ " > /dev/null 2>&1" 
    ^ " && ../sac_c_parser/test/build/ebpf --input-file=" ^ tmpfile ^ " --output-file=" ^ outfile ^ " 1>" ^ !serverroot.path ^ "cstar_output/" ^"log_" ^ filename in
  let _ = Unix.system command in
  Queue.enqueue NotifQueue.q (SymFileResult {SymFileResultParams.filepath = outfile});
  return () *)
  
let on_workspaceDidChangeConfiguration params = 
  let Lsp.Types.DidChangeConfigurationParams.{ settings } = params in
  let settings = Settings.t_of_yojson settings in
  do_configuration settings;
  return ()