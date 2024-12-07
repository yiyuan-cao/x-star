(* open Lsp.Types *)
open Core
open Ppx_yojson_conv_lib.Yojson_conv.Primitives

module Notification = struct

  module Client_ = struct

    module ShowSymParams = struct

      type t = {
        filepath : string;
        line : int;
      } [@@deriving yojson]

    end

    module ShowSymFileParams = struct

      type t = {
        filepath : string;
      } [@@deriving yojson]

    end

    type t =
    | Std of Lsp.Client_notification.t
    | ShowSym of ShowSymParams.t
    (* | ShowSymFile of ShowSymFileParams.t *)

    let of_jsonrpc (Jsonrpc.Notification.{ method_; params; _ } as notif) =
      let open Lsp.Import.Result.O in
      match method_ with
      | "cstar/showsym" ->
        let+ params = Lsp.Import.Json.message_params params ShowSymParams.t_of_yojson in
        ShowSym params
      (* | "cstar/showsymfile" ->
        let+ params = Lsp.Import.Json.message_params params ShowSymFileParams.t_of_yojson in
        ShowSymFile params *)
      | _ ->
        let+ notif = Lsp.Client_notification.of_jsonrpc notif in 
        Std notif
        
  end

  module Server_ = struct

    module SymResultParams = struct
      
      type t = {
        linenum: int; 
        ghostlines: string list;
      } [@@deriving yojson]

    end

    module SymFileResultParams = struct
      
      type t = {
        filepath: string; 
      } [@@deriving yojson]

    end

    module HoverfileResultParams = struct
      
      type t = {
        filepath: string; 
        lasttime: string;
      } [@@deriving yojson]

    end

    type t =
    | Std of Lsp.Server_notification.t
    | SymResult of SymResultParams.t
    | SymFileResult of SymFileResultParams.t
    | HoverfileResult of HoverfileResultParams.t

    let to_jsonrpc = function
      | Std notification ->
        Lsp.Server_notification.to_jsonrpc notification
      | SymResult params ->
        let method_ = "cstar/symResult" in
        let params = SymResultParams.yojson_of_t params in
        let params = Some (Jsonrpc.Structured.t_of_yojson params) in
        Jsonrpc.Notification.{ method_; params }
      | SymFileResult params ->
        let method_ = "cstar/symfileResult" in
        let params = SymFileResultParams.yojson_of_t params in
        let params = Some (Jsonrpc.Structured.t_of_yojson params) in
        Jsonrpc.Notification.{ method_; params }
      | HoverfileResult params ->
        let method_ = "cstar/hoverfileTime" in
        let params = HoverfileResultParams.yojson_of_t params in
        let params = Some (Jsonrpc.Structured.t_of_yojson params) in
        Jsonrpc.Notification.{ method_; params }

    end

end

module NotifQueue = struct
  let q : Notification.Server_.t Queue.t = Queue.create ()
end