let _ = 
  let _ = Format.err_formatter in
  Topcommon.set_paths ();
  Topcommon.initialize_toplevel_env ();
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> exit 0));
  ()

let _ = 
  let run_toplevel code =
    let as_buf = Lexing.from_string code in
    let parsed = !Toploop.parse_toplevel_phrase as_buf in
    ignore (Toploop.execute_phrase false Format.std_formatter parsed) 
  in
    Callback.register "run_toplevel" run_toplevel

let _ =
  let expose_toplevel name =
    let value = Topeval.getvalue name in
    Callback.register name value
  in
    Callback.register "expose_toplevel" expose_toplevel
