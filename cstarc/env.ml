open Ast

(** Architecture-dependent parameters for PowerPC. *)
let ptr64 = true


(** Composite Environment. *)
type struct_or_union = Struct | Union 

type composite = 
  { co_su: struct_or_union
  ; co_members: (typ * ident) list 
  ; co_sizeof: int
  ; co_alignof: int }

module StrMap = Map.Make (String)
type composite_env = composite StrMap.t
let co_ctx : composite_env ref = ref StrMap.empty


(* Calculate size and alignment of type. *)
let rec sizeof = 
  function
  | Tvoid -> 1
  | T_Bool -> 1
  | Tint -> 4
  | Tunsigned -> 4 
  | Tptr _ -> if ptr64 then 8 else 4
  | Tarray (t, e) -> 
    ( match e with 
      | Some { value = Some (Cinteger n); _ } -> 
            sizeof t * (Int.max n 0)
      | _ -> 0 )
  | Tstruct id ->
      List.fold_left 
        (fun acc (t, _) -> acc + (sizeof t)) 0 
            (StrMap.find id !co_ctx).co_members 
  | Tunion id ->
      List.fold_left 
        (fun acc (t, _) -> Int.max acc (sizeof t)) 0 
            (StrMap.find id !co_ctx).co_members 
  | _ -> failwith "sizeof: error type."

let rec alignof = 
  function
  | Tvoid -> 1
  | T_Bool -> 1
  | Tint -> 4
  | Tunsigned -> 4 
  | Tptr _ -> if ptr64 then 8 else 4
  | Tarray (t, _) -> alignof t
  | Tstruct id | Tunion id ->
      List.fold_left 
        (fun acc (t, _) -> Int.max acc (alignof t)) 1 
            (StrMap.find id !co_ctx).co_members 
  | _ -> failwith "sizeof: error type."


(* Declare a composite type and update composite environment. *)
let composite_decl =
  function 
  | Tstructdecl (Some id, fs) -> 
    ( co_ctx := !co_ctx 
        |> StrMap.update id 
          (function _ -> 
              Some { co_su = Struct
                   ; co_members = fs
                   ; co_sizeof = 0 
                   ; co_alignof = 1 });
      co_ctx := !co_ctx 
        |> StrMap.update id 
          (function _ -> 
              Some { co_su = Struct
                   ; co_members = fs
                   ; co_sizeof = sizeof (Tstruct id) 
                   ; co_alignof = alignof (Tstruct id) }); 
      Printf.printf "size of type %s is %d\n" id (sizeof (Tstruct id));
      Printf.printf "alignment of type %s is %d\n" id (alignof (Tstruct id));
    )
  | Tuniondecl (Some id, fs) ->
    ( co_ctx := !co_ctx 
        |> StrMap.update id 
          (function _ -> 
              Some { co_su = Union
                   ; co_members = fs
                   ; co_sizeof = 0 
                   ; co_alignof = 1 });
      co_ctx := !co_ctx 
        |> StrMap.update id 
          (function _ -> 
              Some { co_su = Union
                   ; co_members = fs
                   ; co_sizeof = sizeof (Tunion id) 
                   ; co_alignof = alignof (Tunion id) }); 
    )
  | _ -> ()


(* Calculate field offset with C_type and field name. *)
let rec field_ofs t fid = 
  match t with 
  | Tstruct tid ->
    ( match StrMap.find_opt tid !co_ctx with 
      | None -> failwith "field_ofs: struct not declared."
      | Some co -> field_ofs_aux fid co.co_members )
  | _ -> failwith "field_ofs: not a struct."
and field_ofs_aux id = function
  | [] -> failwith "field_ofs: field name not found."
  | (t, i) :: fs -> if String.equal id i then 0 else (sizeof t) + field_ofs_aux id fs


(* Unfinished. *)
let declaration_action = function
  | Ddecltype (t, _) -> composite_decl t;
  | _ -> ()

let handle program = 
  program |> List.iter declaration_action
