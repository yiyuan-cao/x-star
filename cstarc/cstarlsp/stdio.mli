type channel = {input: Async.Reader.t; output: Async.Writer.t}

val write : channel -> string -> unit Async.Deferred.t

val read : channel -> string option Async.Deferred.t

val stdio : channel Lazy.t
