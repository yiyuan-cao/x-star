(*
   Jacques-Henri Jourdan, Inria Paris
   François Pottier, Inria Paris

   Copyright (c) 2016-2017, Inria
   All rights reserved.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:
   * Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
   * Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
   * Neither the name of Inria nor the
   names of its contributors may be used to endorse or promote products
   derived from this software without specific prior written permission.

   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
   ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
   DISCLAIMED. IN NO EVENT SHALL INRIA BE LIABLE FOR ANY
   DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
   (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
   LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
   ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
   SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* Modified by Yiyuan Cao *)

open Core
open Lexer

let open_file filename =
  let ic =
    if String.(filename = "-") then In_channel.stdin
    else In_channel.create ~binary:false filename
  in
  let lexbuf = Lexing.from_channel ic in
  lexbuf

let print_position outx lexbuf =
  Lexing.(
    let pos = lexbuf.lex_curr_p in
    fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1) )

let command =
  Command.basic ~summary:"C* compiler"
    ~readme:(fun () ->
      "This is a C23 compliant parser written in OCaml, specially designed \
       for constructing C* ASTs. It reads a preprocessed C file in standard \
       input and raises an exception if it contains invalid syntax." )
    Command.Let_syntax.(
      let%map_open input_file = anon ("input_file" %: string) in
      fun () ->
        let lexbuf = open_file input_file in
        try
          let ast = Parser.translation_unit_file lexer lexbuf in
          Printf.printf "%s\n"
            (Printer.Render.render_to_string (Printer.program_to_doc ast))
        with
        | Parser.Error ->
            fprintf stderr "%a: syntax error\n" print_position lexbuf ;
            exit 1
        | Failure s ->
            fprintf stderr "%a: %s\n" print_position lexbuf s ;
            exit 1 )

let () = Command_unix.run command
