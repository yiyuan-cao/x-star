let server_not_initialized id message =
  Jsonrpc.Response.Error.make ~code:ServerNotInitialized ~message ()
  |> Jsonrpc.Response.error id

let request_failed id message =
  Jsonrpc.Response.Error.make ~code:RequestFailed ~message ()
  |> Jsonrpc.Response.error id
