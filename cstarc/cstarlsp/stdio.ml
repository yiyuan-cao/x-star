open Core
open Async

let parse_header line =
  let open Option.Let_syntax in
  let%map colon = String.substr_index line ~pattern:": " in
  let key = String.sub line ~pos:0 ~len:colon in
  let value =
    String.sub line ~pos:(colon + 2) ~len:(String.length line - colon - 2)
  in
  (key, value)

type header = {mutable content_length: int}

let rec read_header channel header =
  match%bind Reader.read_line channel with
  | `Eof -> return None
  | `Ok buf ->
      let buf = String.strip buf in
      if String.is_empty buf then return (Some ()) (* end of header *)
      else
        let key, value =
          parse_header buf |> Option.value_exn ~message:"Malformed header"
        in
        if String.(uppercase key = uppercase "Content-Length") then
          header.content_length <- int_of_string value ;
        read_header channel header

type channel = {input: Reader.t; output: Writer.t}

let write channel msg =
  eprintf "< %s\n" msg ;
  Writer.writef channel.output "Content-Length: %d\r\n\r\n"
    (String.length msg) ;
  Writer.write channel.output msg ;
  Writer.flushed channel.output

let read channel =
  let header = {content_length= -1} in
  match%bind read_header channel.input header with
  | None -> return None
  | Some () -> (
      let buf = Bytes.create header.content_length in
      match%map
        Reader.really_read channel.input buf ~len:header.content_length
      with
      | `Eof _ -> failwith "Unexpected EOF"
      | `Ok ->
          let buf = Bytes.to_string buf in
          eprintf "> %s\n" buf ; Some buf )

let stdio : channel Lazy.t =
  lazy {input= Lazy.force Reader.stdin; output= Lazy.force Writer.stdout}
