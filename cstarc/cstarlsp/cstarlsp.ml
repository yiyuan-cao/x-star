open Core
open Async

let _ =
  Cstarparse.Context.declare_typedefname "thm" ;
  Cstarparse.Context.declare_typedefname "lemma" ;
  Cstarparse.Context.declare_typedefname "term" ;
  Cstarparse.Context.declare_typedefname "rewrites_item" ;
  Cstarparse.Context.declare_typedefname "slval"

type args = {host: string}

let main (args : args) =
  let host = args.host in
  eprintf "[CStar LSP] Host: %s\n" host ;
  let stdio = Lazy.force Cstarlsplib.Stdio.stdio in
  Cstarlsplib.Server.run stdio

let command =
  Command.async ~summary:"CStar LSP"
    (let%map_open.Command host =
       flag "-host"
         (optional_with_default "127.0.0.1:5000" string)
         ~doc:" HOL Server (IP:PORT)"
     in
     fun () -> main {host} )

let () = Command_unix.run ~version:"0.2" command
