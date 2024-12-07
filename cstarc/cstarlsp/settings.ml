open Ppx_yojson_conv_lib.Yojson_conv.Primitives

module HolLitePath = struct

  type t = {
    path: string;
  } [@@deriving yojson]

  let t_of_yojson = function
  | `String s -> {path = s}
  | _ -> Yojson.json_error @@ "invalid value "
    
end

module BDWGCFlag = struct

  type t = {
    flags: string;
  } [@@deriving yojson]
  
  let t_of_yojson = function
  | `String s -> {flags = s}
  | _ -> Yojson.json_error @@ "invalid value "

end

type t = {
  hollitepath: HolLitePath.t;
  bdwgcflag: BDWGCFlag.t;
} [@@deriving yojson] [@@yojson.allow_extra_fields]