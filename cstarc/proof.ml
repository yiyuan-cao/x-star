open Core
open Ast

let escape_for_c_string s =
  let buffer = Buffer.create (String.length s) in
  String.iter s ~f:(fun c ->
      match c with
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '"' -> Buffer.add_string buffer "\\\""
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\t' -> Buffer.add_string buffer "\\t"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\000' -> Buffer.add_string buffer "\\0"
      | _ -> Buffer.add_char buffer c ) ;
  let literial = Buffer.contents buffer in
  {value= s; literal= [literial]}

let anti_quoted =
  let open Re in
  seq
    [ char '$'
    ; char '{'
    ; group (any |> rep1 |> non_greedy)
    ; char ':'
    ; group (any |> rep1 |> non_greedy)
    ; char '}' ]
  |> compile

let make_proof_of_term term =
  let s = escape_for_c_string term in
  let s = Econst (Cstring s) in
  Ecall (Evar "parse_term", [s])

let make_proof_of_quoted quoted =
  let buffer = Buffer.create (String.length quoted) in
  Re.split_full anti_quoted quoted
  |> List.fold_left ~init:[] ~f:(fun substs m ->
         match m with
         | `Text s ->
             Buffer.add_string buffer s ;
             substs
         | `Delim g ->
             let name = Re.Group.get g 1 in
             let typ = Re.Group.get g 2 in
             Buffer.add_string buffer name ;
             (name, typ) :: substs )
  |> List.fold_right
       ~init:(Buffer.contents buffer |> make_proof_of_term)
       ~f:(fun (name, typ) expr ->
         Ecall
           ( Evar "subst"
           , [Evar name; make_proof_of_term (sprintf "%s:%s" name typ); expr]
           ) )

let rec make_proof_of_expr = function
  | Econst (Cquoted s) -> make_proof_of_quoted s
  | Econst c -> Econst c
  | Ecomplit (typ, init) -> Ecomplit (typ, make_proof_of_init init)
  | Ebackquoted _ -> failwith "Not implemented: backquoted"
  | Evar s -> Evar s
  | Eunary (op, expr) -> Eunary (op, make_proof_of_expr expr)
  | Ebinary (op, expr1, expr2) ->
      Ebinary (op, make_proof_of_expr expr1, make_proof_of_expr expr2)
  | Ecall (expr, exprs) ->
      Ecall (make_proof_of_expr expr, List.map exprs ~f:make_proof_of_expr)
  | Esizeofexpr expr -> Esizeofexpr (make_proof_of_expr expr)
  | Esizeoftyp typ -> Esizeoftyp typ
  | Ecast (typ, expr) -> Ecast (typ, make_proof_of_expr expr)
  | Econditional (expr1, expr2, expr3) ->
      Econditional
        ( make_proof_of_expr expr1
        , make_proof_of_expr expr2
        , make_proof_of_expr expr3 )
  | Elet_data_at _ -> failwith "Not implemented: Elet_data_at"

and make_proof_of_init = function
  | Init_single expr -> Init_single (make_proof_of_expr expr)
  | Init_struct inits ->
      Init_struct
        (List.map inits ~f:(fun (ident, init) ->
             (ident, make_proof_of_init init) ) )
  | Init_array inits -> Init_array (List.map inits ~f:make_proof_of_init)

(*and declaration =
  | Ddeclvar of typ * ident * init option * range
      (** variable declaration. *)
  | Ddeclfun of funsym * attribute list  (** function declaration. *)
  | Ddecltype of typ * range  (** type definition. *)
  | Ddecltypedef of ident * typ * range  (** type definition. *)
  | Ddeffun of funsym * attribute list * stmt  (** function definition. *)
  | Dattribute of attribute * range  (** attribute declaration. *)*)

(*and stmt =
  | Sskip of attribute list * range
  | Sblock of stmt list * range
  | Sexpr of expr * attribute list * range
  | Sif of expr * stmt * stmt option * attribute list * range
  | Swhile of expr * stmt * attribute list * range
      (** optionally preceded by a invariant (written as [/*@ invariant <expr>*/])*)
  | Sbreak of range
  | Scontinue of range
  | Sreturn of expr option * range
  | Sdecl of declaration * attribute list (** local declarations. *)*)

(* let rec make_proof_of_stmt = function
     | Sskip (_, r) -> [Sskip ([], r)]
     | Sblock (stmts, r) -> [Sblock (List.map stmts ~f:make_proof_of_stmt, r)]
     | Sexpr (expr, _, r) -> [Sexpr (make_proof_of_expr expr, [], r)]
     | Sif (expr, stmt1, stmt2, _, r) ->
         [ Sif
             ( make_proof_of_expr expr
             , make_proof_of_stmt stmt1
             , Option.map stmt2 ~f:make_proof_of_stmt
             , []
             , r ) ]
     | Swhile (expr, stmt, _, r) ->
         [Swhile (make_proof_of_expr expr, make_proof_of_stmt stmt, [], r)]
     | Sbreak r -> [Sbreak r]
     | Scontinue r -> [Scontinue r]
     | Sreturn (Some expr, r) -> [Sreturn (Some (make_proof_of_expr expr), r)]
     | Sreturn (None, r) -> [Sreturn (None, r)]
     | Sdecl (decl, _) ->
         make_proof_of_decl decl |> List.map ~f:(fun d -> Sdecl (d, []))
*)

let flatten_stmts = function
  | [] -> Sskip ([], dummy_range)
  | [stmt] -> stmt
  | stmts -> Sblock (stmts, dummy_range)

let rec make_proof_of_stmt ~only_attrs = function
  | Sskip (attrs, r) ->
      make_proof_of_local_cstar_attrs attrs
      @ if only_attrs then [] else [Sskip ([], r)]
  | Sblock (stmts, r) ->
      [ Sblock
          ( List.map stmts ~f:(fun s -> make_proof_of_stmt s ~only_attrs)
            |> List.concat
          , r ) ]
  | Sexpr (expr, attrs, r) ->
      make_proof_of_local_cstar_attrs attrs
      @ if only_attrs then [] else [Sexpr (make_proof_of_expr expr, [], r)]
  | Sif (expr, stmt1, stmt2, attrs, r) ->
      make_proof_of_local_cstar_attrs attrs
      @
      if only_attrs then
        make_proof_of_stmt stmt1 ~only_attrs
        @ Option.value_map stmt2 ~default:[] ~f:(fun s ->
              make_proof_of_stmt s ~only_attrs )
      else
        [ Sif
            ( make_proof_of_expr expr
            , make_proof_of_stmt stmt1 ~only_attrs |> flatten_stmts
            , Option.map stmt2 ~f:(fun s ->
                  make_proof_of_stmt s ~only_attrs |> flatten_stmts )
            , []
            , r ) ]
  | Swhile (expr, stmt, attrs, r) ->
      make_proof_of_local_cstar_attrs attrs
      @
      if only_attrs then make_proof_of_stmt stmt ~only_attrs
      else
        [ Swhile
            ( make_proof_of_expr expr
            , make_proof_of_stmt stmt ~only_attrs |> flatten_stmts
            , []
            , r ) ]
  | Sbreak r -> if only_attrs then [] else [Sbreak r]
  | Scontinue r -> if only_attrs then [] else [Scontinue r]
  | Sreturn (Some expr, r) ->
      if only_attrs then [] else [Sreturn (Some (make_proof_of_expr expr), r)]
  | Sreturn (None, r) -> if only_attrs then [] else [Sreturn (None, r)]
  | Sdecl (decl, _) ->
      make_proof_of_local_decl decl ~only_attrs
      |> List.map ~f:(fun d -> Sdecl (d, []))

and make_proof_of_local_decl ~only_attrs = function
  | Ddeclvar (typ, ident, init, range) ->
      if only_attrs then []
      else
        [Ddeclvar (typ, ident, Option.map init ~f:make_proof_of_init, range)]
  | Ddeclfun (funsym, _) -> if only_attrs then [] else [Ddeclfun (funsym, [])]
  | Ddecltype (typ, range) -> [Ddecltype (typ, range)]
  | Ddecltypedef (ident, typ, range) -> [Ddecltypedef (ident, typ, range)]
  | Ddeffun _ -> failwith "Not implemented: Local function definition"
  | Dattribute _ -> failwith "Not implemented: Local attribute"

and make_proof_of_local_cstar_attrs attrs =
  List.map attrs ~f:(function Acstar attr ->
      make_proof_of_local_cstar_attr attr )
  |> List.concat

and make_proof_of_local_cstar_attr = function
  | Aproof stmts ->
      List.map stmts ~f:(fun s -> make_proof_of_stmt s ~only_attrs:false)
      |> List.concat
  | Aassert expr ->
      let expr = make_proof_of_expr expr in
      [Sexpr (Ebinary (Oassign, Evar "__state", expr), [], dummy_range)]
  | Ainvariant expr ->
      let expr = make_proof_of_expr expr in
      [Sexpr (Ebinary (Oassign, Evar "__state", expr), [], dummy_range)]
  | _ -> []

let make_proof_of_global_cstar_attr = function
  | Afunction (Ddeffun (funsym, _, stmt)) ->
      let stmt =
        make_proof_of_stmt stmt ~only_attrs:false |> flatten_stmts
      in
      [Ddeffun (funsym, [], stmt)]
  | _ -> []

let make_proof_of_global_decl = function
  | Dattribute (Acstar attr, _) -> make_proof_of_global_cstar_attr attr
  | Ddeffun (funsym, _, stmt) ->
      let _, ident, _, r = funsym in
      let funsym = (Tvoid, ident, [], r) in
      let stmt = make_proof_of_stmt stmt ~only_attrs:true |> flatten_stmts in
      [Ddeffun (funsym, [], stmt)]
  | Ddecltype (t, r) -> [Ddecltype (t, r)]
  | Ddecltypedef (i, t, r) -> [Ddecltypedef (i, t, r)]
  | Ddeclvar (t, id, i, r) -> [Ddeclvar (t, id, i, r)]
  | _ -> []

let make_proof program =
  List.map program ~f:make_proof_of_global_decl |> List.concat
