let topeval code =
  let as_buf = Lexing.from_string code in
  let parsed = !Toploop.parse_toplevel_phrase as_buf in
  ignore (Toploop.execute_phrase true Format.std_formatter parsed);;

let ensure_term (t: Hol.term) = t;;
let ensure_type (t: Hol.hol_type) = t;;

let parse_term_from_string term : Hol.term =
  topeval ("let pt_internal = ensure_term(`" ^ term ^ "`);;");
  Topeval.getvalue "pt_internal" |> Obj.obj;;

let parse_type_from_string type_str : Hol.hol_type =
  topeval ("let pt_internal = ensure_type(`" ^ type_str ^ "`);;");
  Topeval.getvalue "pt_internal" |> Obj.obj;;

let parse_conv_from_string conv_str = 
  topeval ("let pt_internal = " ^ conv_str ^ ";;");
  Topeval.getvalue "pt_internal" |> Obj.obj;;

let SPURE_REWRITE_CONV thm tm = PURE_REWRITE_CONV [thm] tm;;
let SPURE_REWRITE_RULE thm t = PURE_REWRITE_RULE [thm] t;;
let SREWRITE_CONV thm tm = REWRITE_CONV [thm] tm;;
let SREWRITE_RULE thm t = REWRITE_RULE [thm] t;;
let SPURE_ONCE_REWRITE_CONV thm tm = PURE_ONCE_REWRITE_CONV [thm] tm;;
let SPURE_ONCE_REWRITE_RULE thm t = PURE_ONCE_REWRITE_RULE [thm] t;;
let SONCE_REWRITE_CONV thm tm = ONCE_REWRITE_CONV [thm] tm;;
let SONCE_REWRITE_RULE thm t = ONCE_REWRITE_RULE [thm] t;;

let INDUCT_INSTANTIATE ind tm1 tm2 = 
  INSTANTIATE (term_match [] tm1 tm2) (SPEC_ALL ind);;

let new_constant_helper constname consttype = 
  let ex_type = try Some(get_const_type constname) with Failure _ -> None in
  match ex_type with
  | Some t when t = consttype -> ()
  | Some _ -> failwith "new_constant_helper: constant already exists with different type"
  | None -> new_constant (constname, consttype);;

let new_type_helper typename arity = 
  let arity = int_of_string arity in
  let ex_arity = try Some(get_type_arity typename) with Failure _ -> None in
  match ex_arity with
  | Some a when a = arity -> ()
  | Some _ -> failwith "new_type_helper: type already exists with different arity"
  | None -> new_type (typename, arity);;

let rec dump_coq_type ty = 
  if is_vartype ty then
    dest_vartype ty
  else if is_type ty then
    let (t, args) = dest_type ty in
    if args = [] then
      t
    else if t == "bool" then
      "Prop"
    else if t == "fun" then
      let (t1, t2) = dest_fun_ty ty in
        "(" ^ dump_coq_type t1 ^ " -> " ^ dump_coq_type t2 ^ ")"
    else
      let args_str = map dump_coq_type args |> String.concat " " in
        "(" ^ t ^ " " ^ args_str ^ ")"
  else
    failwith "dump_coq_type: unknown type";;

let rec dump_coq_term with_ty tm = 
  print_term tm;
  print_newline();
  if is_forall tm then
    let (v, a) = dest_forall tm in
    "(forall " ^ dump_coq_term true v ^ ", " ^ dump_coq_term false a ^ ")"
  else if is_exists tm then
    let (v, a) = dest_exists tm in
    "(exists " ^ dump_coq_term true v ^ ", " ^ dump_coq_term false a ^ ")"
  else if is_conj tm then
    let (a, b) = dest_conj tm in
    "(" ^ dump_coq_term false a ^ " /\\ " ^ dump_coq_term false b ^ ")"
  else if is_disj tm then
    let (a, b) = dest_disj tm in
    "(" ^ dump_coq_term false a ^ " \\/ " ^ dump_coq_term false b ^ ")"
  else if is_neg tm then
    let a = dest_neg tm in
    "~(" ^ dump_coq_term false a ^ ")"
  else if is_imp tm then
    let (a, b) = dest_imp tm in
    "(" ^ dump_coq_term false a ^ " -> " ^ dump_coq_term false b ^ ")"
  else if is_iff tm then
    let (a, b) = dest_iff tm in
    "(" ^ dump_coq_term false a ^ " <-> " ^ dump_coq_term false b ^ ")"
  (* iff must be handled before eq, since it is also an equality *)
  else if is_eq tm then
    let (a, b) = dest_eq tm in
    "(" ^ dump_coq_term false a ^ " = " ^ dump_coq_term false b ^ ")"
  (* Binders must be handled before conb, since they are also applications *)
  else if is_comb tm then
    let (f, arg) = dest_comb tm in
    "(" ^ dump_coq_term false f ^ " " ^ dump_coq_term false arg ^ ")"
  else if is_var tm then
    let (v, ty) = dest_var tm in
    if with_ty then
      "(" ^ v ^ ": " ^ dump_coq_type ty ^ ")"
    else
      v
  else if is_const tm then
    let (c, ty) = dest_const tm in
    if with_ty then
      "(" ^ c ^ ": " ^ dump_coq_type ty ^ ")"
    else
      c
  else if is_numeral tm then
    let n = dest_numeral tm in
    string_of_num n
  else
    failwith "dump_coq_term: unknown term";;

let dump_coq_thm name thm = 
  if hyp thm |> length != 0 then
    failwith "dump_coq_thm: theorem has hypotheses";
  let tm = concl thm in
  let tm_str = dump_coq_term false tm in
  "Axiom " ^ name ^ " : " ^ tm_str ^ ".";;

let mk_abs_aux tm1 tm2 = mk_abs (tm1, tm2);;
let mk_comb_aux tm1 tm2 = mk_comb (tm1, tm2);;

let ssubst tm1 tm2 tm = subst[tm1, tm2] tm;;

let apply_conv conv tm = conv tm;;

let hypth th = hd (hyp th);;
let equals_term t1 t2 = t1 = t2;;

let ARITH_RULE_SAFE t = try ARITH_RULE t with Failure _ -> TRUTH;;
let INT_ARITH_SAFE t = try INT_ARITH t with Failure _ -> TRUTH;;