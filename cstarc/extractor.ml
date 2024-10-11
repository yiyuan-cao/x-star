open Ast
open Env 

(* Note: now we don't support range information in extraction. *)
let _range : range = {start_p = {line_no = 0; col_no = 0}; end_p = {line_no = 0; col_no = 0}}

(* Default variable suffix for special cases. *)
let _var = "_var"

type form = String | Term | Type

(* Record of calling a HOL-light interface. *)
type command = { lval: ident option; func: string; params: (form * string) list }

(* Global declarations of ghost definitions. *)
let ghost_decl : declaration list ref = ref []
(* Body of function `ghost_function()`. *)
let ghost_function : stmt list ref = ref []
(* Turning a HOL-light calling into a C* statement. *)
let register_ghost_def (cmd: command) = 
  match cmd.lval with 
  | None -> 
    ( ghost_function := 
        Sexpr (
          Ecall ( Evar cmd.func, 
                  List.map (fun (fm, str) -> 
                    let str = Cstring { value = str; literal = [str] } in
                      match fm with 
                      | String -> Econst str
                      | Term -> Ecall (Evar "parse_term", [Econst str])
                      | Type -> Ecall (Evar "parse_type", [Econst str])
                  ) cmd.params
                ),
          [], _range ) :: !ghost_function ;
    )
  | Some lval -> 
      let ty = 
        match cmd.func with 
        | "define" | "new_axiom" -> "thm"
        | "define_type"          -> "indtype"
        | _                      -> failwith "push_ghost_def: unsupported HOL-light interface." 
      in 
      ghost_decl :=
        Ddeclvar (Tnamed ty, lval, None, _range)
          :: !ghost_decl; 
    ( ghost_function := 
        Sexpr (
          Ebinary (Oassign, Evar lval, 
            Ecall ( Evar cmd.func, 
                    List.map (fun (fm, str) -> 
                      let str = Cstring { value = str; literal = [str] } in
                        match fm with 
                        | String -> Econst str
                        | Term -> Ecall (Evar "parse_term", [Econst str])
                        | Type -> Ecall (Evar "parse_type", [Econst str])
                    ) cmd.params
                  ) 
          ),
          [], _range ):: !ghost_function;
    )

(* Set of all constructor names. *)
(* Note: we use `f a b` syntax when writing constructors, 
   and we use `f(a, b)` syntax otherwise. *)
module StrSet = Set.Make (String)
let constr_names = ref StrSet.empty


(** Extraction. *)
(* Note: we don't carefully handle operator precedence in this part, 
   just adding enough and maybe redundent parentheses. We can see 
   pretty-printed expression in HOL-light output.  *)
let constant_to_str = 
  function
  | Cinteger i -> Int.to_string i 
  | Cboolean b -> Bool.to_string b 
  | Cstring str -> str.value
  | Cnullval -> "(&0)" (* Dead code? `NULL` is Evar "NULL". *)

let typ_to_str = 
  function 
  | T_Bool -> "bool"
  | Tint -> "int"
  | Tunsigned -> "num"
  | Tprop -> "bool"
  | Thprop -> "HPROP"
  | Tptr _ -> "PTR"
  | Tarray _ -> "PTR"
  | Tnamed id -> id 
  | _ -> failwith "typ_to_str: not a spec type."

let params_ident_to_str ?(var_suffix = String.empty) =
  List.fold_left (fun acc (_, id) -> acc ^ " " ^ id ^ var_suffix) ""
  
let params_to_binder_str ?(var_suffix = String.empty) = 
  function
  | [] -> "" 
  | ps -> "!" 
      ^ ( ps |> List.concat_map (fun (ty, id) -> 
                    ["(" ^ id ^ var_suffix ^ ":" ^ typ_to_str ty ^ ")"]) 
             |> String.concat " " )
      ^ ". " 

let constrs_to_str constrs = 
  constrs 
    |> List.concat_map (fun (id, ps) -> 
        [id ^ List.fold_left (fun acc (ty, _) -> acc ^ " " ^ typ_to_str ty) "" ps]) 
    |> String.concat " | "

let rec expr_to_str =
  let parens str = "(" ^ str ^ ")" in 
    function 
    | Econst c -> constant_to_str c  
    | Ebackquoted s -> s 
    | Evar v -> if String.equal v "NULL" then "(&0)" else v 
    | Eunary (op, e) -> 
      ( match op with 
        | Ominus -> "-"
        | Oplus -> "+"
        | Olognot -> "~"
        (* TODO: other operators. *)
        | _ ->  "unary_expr_to_str: unsupported operator."
      ) ^ parens (expr_to_str e)
    | Ebinary (op, e1, e2) -> 
      ( let op = 
        ( match op with 
          | Omul -> `Op "*" 
          | Odiv -> `Op "/" (* MOD: only for `:num` in HOL-light. *)
          | Omod -> `Op "MOD" 
          | Oadd -> `Op "+"
          | Osub -> `Op "-"
          | Olt -> `Op "<"
          | Ogt -> `Op ">"
          | Ole -> `Op "<="
          | Oge -> `Op ">="
          | Oeq -> `Op "="
          | One -> `One 
          | Ologand -> `Op "&&"
          | Ologor -> `Op "||"
          (* TODO: bit operations. *)
          | Obitand -> `Func "word_and"
          | Obitor -> `Func "word_or"
          | Obitxor -> `Func "word_xor"
          | Obitrsh -> `Func "word_ushr"
          | Obitlsh -> `Func "word_shl"
          | Oassign -> `Op "="
          | Osep -> `Op "SEPCONJ"
          | Osepand -> `Op "SEPAND"
          (* TODO: array indexing. *)
          | _ -> failwith "binary_expr_to_str: unsupported operator."
        ) in 
        match op with
        | `Op op -> parens (expr_to_str e1) ^ op ^ parens (expr_to_str e2)
        | `Func word_op -> word_op ^ parens (expr_to_str e1) ^ parens (expr_to_str e2)
        | `One -> "~" ^ parens (expr_to_str e1) ^ "=" ^ parens (expr_to_str e2)
      )
    | Ecall (Evar func, exprs) -> 
      if (String.equal func "DATA_AT")
        then 
          failwith "data_at: unsupported."
          (* TODO: DATA_AT predicate. *) 
        else 
          ( match (StrSet.find_opt func !constr_names) with 
            | None -> func ^ 
                parens (exprs |> List.concat_map (fun e -> [expr_to_str e]) |> String.concat ",")
            | Some _ -> func 
                ^ (exprs |> List.concat_map (fun e -> [parens (expr_to_str e)]) |> String.concat "") )
    | Ecast (ty, e) -> 
      (typ_to_str ty) ^ ":" ^ (expr_to_str e)
    | Econditional (e, c1, c2) -> 
      "if" ^ parens (expr_to_str e)
        ^ "then" ^ parens (expr_to_str c1)
        ^ "else" ^ parens (expr_to_str c2)
    | _ -> failwith "expr_to_str: unsupported expression. "
and init_to_str = 
  function 
  | Init_single e -> expr_to_str e 
  | _ -> "init_to_str: unsupported. " (* TODO: init struct/array. *)


let func_to_str ps stmt = 
  let parens str = "(" ^ str ^ ")" in 
  (* Local variables type information. *)
  (* Note: now we only clear local variable context after exiting a function. *)
  let local_var : (typ StrMap.t) ref = ref StrMap.empty in 
  let decl_var id ty = local_var := StrMap.add id ty !local_var in 
  let typ_var id = StrMap.find id !local_var in
  let typ_suffix = 
    function
    | T_Bool -> "_BOOL"
    | Tint -> "_INT"
    | Tunsigned -> "_UINT"
    | Tptr _ -> "_PTR"
    | Tarray _ -> failwith "data_at: unsupported array."
    | Tstruct _ -> failwith "data_at: unsupported struct."
    | Tunion _ -> failwith "data_at: unsupported union."
    | _ -> failwith "data_at: wrong type."
  in
  let rec stmt_to_str =
    function 
    | Sskip (_, _)-> ""
    | Sblock (stmts, _) -> 
        List.fold_right 
          (fun stmt acc -> parens (stmt_to_str stmt ^ acc)) stmts "" 
    | Sexpr (Elet_data_at (e, ty, id), _, _) -> 
      ( let expr_str = 
          ( match e with 
            | Eunary (Oaddrof, e) -> 
              ( match e with 
                | Evar p -> 
                    parens ("DATA_AT" ^ typ_suffix ty ^ parens (p ^ "," ^ id))
                | Eunary ((Oarrow fid), Evar p) -> 
                  ( match (typ_var p) with 
                    | Tptr (Tstruct tid) -> 
                      parens ("DATA_AT" ^ typ_suffix ty ^ parens (p ^ "+" 
                        ^ parens ("&" ^ Int.to_string (field_ofs (Tstruct tid) fid)) ^ "," ^ id)) 
                    | _ -> failwith "let_data_at: use arrow but not a struct pointer." )
                | Eunary ((Odot fid), Evar p) -> 
                  ( match (typ_var p) with 
                    | Tstruct tid -> 
                      parens ("DATA_AT" ^ typ_suffix ty ^ parens (p ^ "+" 
                        ^ parens ("&" ^ Int.to_string (field_ofs (Tstruct tid) fid)) ^ "," ^ id)) 
                    | _ -> failwith "let_data_at: use dot but not a struct." )
                | _ -> failwith "let_data_at: unsupported pointer syntax."
                (* TODO: DATA_AT_STRUCT/ARRAY *)
              )
            | _ -> failwith "let_data_at: unsupported syntax." 
          ) in 
        "SEPEXISTS " ^ parens (id ^ ":" ^ typ_to_str ty) ^ ". "
          ^ expr_str ^ " SEPCONJ " 
      )
    | Sexpr (Ebinary (Oassign, e1, e2), _, _) ->
      "let " ^ expr_to_str e1 ^ "=" ^ expr_to_str e2 ^ " in " 
    | Sif (e, c1, Some c2, _, _) ->
      "if" ^ parens (expr_to_str e)
        ^ "then" ^ parens (stmt_to_str c1)
        ^ "else" ^ parens (stmt_to_str c2)
    | Sreturn (Some e, _) -> expr_to_str e
    | Sdecl (Ddeclvar (ty, id, init, _)) -> 
      decl_var id ty;
      ( match init with 
        | None -> ""
        | Some init -> 
            "let " ^ parens (id ^ ":" ^ typ_to_str ty)
              ^ "=" ^ init_to_str init ^ " in " )
    | _ -> failwith "stmt_to_str: unsupported attribute syntax" in 
  List.iter (fun (ty, id) -> decl_var id ty) ps;
  stmt_to_str stmt


let discriminator_decl constrs = 
  constrs 
    |> List.iter ( 
      fun (id, _) -> 
        let discr_name = "is_" ^ id in 
        let str = 
          constrs 
            |> List.concat_map 
              ( fun (id0, ps0) -> 
                [ "(" ^ params_to_binder_str ~var_suffix:_var ps0
                  ^ discr_name ^ "(" ^ id0 ^ params_ident_to_str ~var_suffix:_var ps0 ^ ")" 
                  ^ " = " ^ (if String.equal id id0 then "T" else "F") ^ ")" ] )
            |> String.concat " && "
          in 
        register_ghost_def 
          { lval = Some discr_name
          ; func = "define"
          ; params = [(Term, str)]};
    ) 

let accessor_decl = 
  List.iter (
    fun (id, ps) -> 
      ps |> List.iter 
        ( fun (_, id0) -> 
          let str =
            params_to_binder_str ~var_suffix:_var ps
            ^ id0 ^ "(" ^ id ^ params_ident_to_str ~var_suffix:_var ps ^ ")"
            ^ " = " ^ id0 ^ _var in
          register_ghost_def
            { lval = Some id0
            ; func = "define"
            ; params = [(Term, str)]}; 
        )
  )

let constructor_decl = 
  List.iter ( fun (id, _) -> 
    constr_names := StrSet.add id !constr_names )

let attribute_decl = 
  function
  | Dattribute (Acstar attr, _) -> 
    ( match attr with 
      | Adatatype { name; constructors } ->
        ( register_ghost_def
            { lval = Some name
            ; func = "define_type"
            ; params = [(String, name ^ " = " ^ constrs_to_str constructors)]
            };
          discriminator_decl constructors;
          accessor_decl constructors;
          constructor_decl constructors;
        )
      | Afunction (Ddeffun ((ty, id, ps, _), _, stmt)) 
      | Arepresentation (Ddeffun ((ty, id, ps, _), _, stmt)) 
      | Apredicate (Ddeffun ((ty, id, ps, _), _, stmt)) -> 
          ( register_ghost_def 
              { lval = None
              ; func = "new_constant"
              ; params = [ (String, id); 
                           (Type, (ps |> List.concat_map (fun (t, _) -> [typ_to_str t]) |> String.concat "#")
                                    ^ "->" ^ typ_to_str ty) ]
              };
            register_ghost_def 
              { lval = Some id 
              ; func = "new_axiom"
              ; params = [ (Term, params_to_binder_str ps ^ id ^ "(" 
                                  ^ (ps |> List.concat_map (fun (_, id) -> [id]) |> String.concat ",")
                                  ^ ")" ^ " = " ^ func_to_str ps stmt) ]
              };
          )
      | _ -> ()
    )
  | _ -> ()

(* Main function with input/output both Ast.program *)
let extractor ast = 
  List.iter attribute_decl ast;
  ghost_function := List.rev !ghost_function;
  (List.rev !ghost_decl) 
    @ [Ddeffun ((Tvoid, "ghost_function", [] , _range), [], Sblock (!ghost_function, _range))]