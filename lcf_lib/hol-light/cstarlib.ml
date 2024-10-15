(* For bounded integer reasoning and bit manipulation *)
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
needs "Library/binary.ml";;
needs "Library/bitsize.ml";;
needs "Library/iter.ml";;

(* Update an association list *)
let rec update_assoc (k, v) = function
  | [] -> [(k, v)]
  | (k', v') :: t -> if k = k' then (k, v) :: t
                   else (k', v') :: (update_assoc (k, v) t)
;;

(* Add a theorem to the search database *)
let add_to_database (name, thm) =
    theorems := update_assoc (name, thm) !theorems
;;

(* Print variables with types *)
let print_typed_var fmt tm =
    let s, ty = dest_var tm in
    pp_print_string fmt ("(" ^ s ^ ":" ^ string_of_type ty ^ ")")
;;

(* Unset multiple subgoals (a lexer option handled by preprocessor) *)
unset_then_multiple_subgoals;;

(* Personal preferences and useful information *)
let set_preference debugging =
    if (debugging) then begin
        (* Show types of variables and constants in terms *)
        print_types_of_subterms := 2;
        (* Print without reversing interface *)
        reverse_interface_mapping := false;
        (* Treat type inventions as errors *)
        type_invention_error := true;
        (* Unset printing verbose symbols like `exists` and `forall` *)
        unset_verbose_symbols ()
    end else begin
        install_user_printer("print_typed_var", print_typed_var);
        reverse_interface_mapping := true;
        type_invention_error := false
    end;
    (* Overload arithmetic interface to `int` by default *)
    prioritize_int ()
;;

set_preference false;;

(* Helper function for uncurrying; C* usually exports an uncurried interfaces (except for operators) *)
let uncurry_def = new_definition
    `uncurry (f : A -> B -> C) = \(x,y). f x y`
;;

(* Commonly used synonyms *)
let () =
    new_type_abbrev ("addr", `:int`);
    new_type_abbrev ("ilist", `:int list`);
;;

(* Get the address of a variable/R-expression in C (represented as a string currently) *)
(* Overload the previous interface ("&", `int_of_num`) *)
let () =
    new_constant ("addr_of", `:string -> addr`);
    (* Warning: is this safe? *)
    the_overload_skeletons := update_assoc ("&", `:A -> int`) !the_overload_skeletons;
    overload_interface ("&", `addr_of`);
    make_overloadable "==" `:A -> A -> B`;
    (* Warning: the notation `==` is used for congruence relations in `int.ml` *)
    overload_interface("==", `(==):A -> A -> (A->A->bool) -> bool`);
    overload_interface("==", `(=):A -> A -> bool`)
;;

(* C scalar types *)
let ctype_induct, ctype_rec = define_type "
    ctype =
        Tchar  | Tuchar  |
        Tshort | Tushort |
        Tint   | Tuint   |
        Tint64 | Tuint64 |
        Tptr
";;

(* Word size in bytes *)
let word_size_def = new_basic_definition
    `word_size = &4`;;

(* Size of a C scalar type in bytes *)
let size_of_def = new_recursive_definition ctype_rec `
    size_of Tchar    = &1 /\
    size_of Tuchar   = &1 /\
    size_of Tshort   = &2 /\
    size_of Tushort  = &2 /\
    size_of Tint     = &4 /\
    size_of Tuint    = &4 /\
    size_of Tint64   = &8 /\
    size_of Tuint64  = &8 /\
    size_of Tptr     = word_size`
;;

(* Alignment requirement of a C scalar type *)
let align_of_def = new_recursive_definition ctype_rec `
    align_of Tchar    = &1 /\
    align_of Tuchar   = &1 /\
    align_of Tshort   = &2 /\
    align_of Tushort  = &2 /\
    align_of Tint     = &4 /\
    align_of Tuint    = &4 /\
    align_of Tint64   = min word_size (&8) /\
    align_of Tuint64  = min word_size (&8) /\
    align_of Tptr     = word_size`
;;

(* Tchar min *)
let tchar_min_def = new_basic_definition
    `tchar_min : int = --(&128)`
;;

(* Tchar max *)
let tchar_max_def = new_basic_definition
    `tchar_max : int = &127`
;;

(* Tuchar min *)
let tuchar_min_def = new_basic_definition
    `tuchar_min : int = &0`
;;

(* Tuchar max *)
let tuchar_max_def = new_basic_definition
    `tuchar_max : int = &255`
;;

(* Tshort min *)
let tshort_min_def = new_basic_definition
    `tshort_min : int = --(&32768)`
;;

(* Tshort max *)
let tshort_max_def = new_basic_definition
    `tshort_max : int = &32767`
;;

(* Tushort min *)
let tushort_min_def = new_basic_definition
    `tushort_min : int = &0`
;;

(* Tushort max *)
let tushort_max_def = new_basic_definition
    `tushort_max : int = &65535`
;;

(* Tint min *)
let tint_min_def = new_basic_definition
    `tint_min : int = --(&2147483648)`
;;

(* Tint max *)
let tint_max_def = new_basic_definition
    `tint_max : int = &2147483647`
;;

(* Tuint min *)
let tuint_min_def = new_basic_definition
    `tuint_min : int = &0`
;;

(* Tuint max *)
let tuint_max_def = new_basic_definition
    `tuint_max : int = &4294967295`
;;

(* Tint64 min *)
let tint64_min_def = new_basic_definition
    `tint64_min : int = --(&9223372036854775808)`
;;

(* Tint64 max *)
let tint64_max_def = new_basic_definition
    `tint64_max : int = &9223372036854775807`
;;

(* Tuint64 min *)
let tuint64_min_def = new_basic_definition
    `tuint64_min : int = &0`
;;

(* Tuint64 max *)
let tuint64_max_def = new_basic_definition
    `tuint64_max : int = &18446744073709551615`
;;

(* Tptr min *)
let tptr_min_def = new_basic_definition
    `tptr_min : int = &0`
;;

(* Tptr max *)
let tptr_max_def = new_basic_definition
    `tptr_max : int = &2 pow (num_of_int word_size * 8) - &1`
;;

(* Size of a type is positive *)
let size_of_gt_0 = prove (
    `!ty. size_of ty > &0`,
    MATCH_MP_TAC ctype_induct THEN
    REWRITE_TAC [word_size_def; size_of_def] THEN
    REPEAT STRIP_TAC THENL
    replicate INT_ARITH_TAC 9
);;
add_to_database ("size_of_gt_0", size_of_gt_0);;

(* Alignment of a type is positive *)
let align_of_gt_0 = prove (
    `!ty. align_of ty > &0`,
    MATCH_MP_TAC ctype_induct THEN
    REWRITE_TAC [word_size_def; align_of_def] THEN
    REPEAT STRIP_TAC THENL
    replicate INT_ARITH_TAC 9
);;
add_to_database ("align_of_gt_0", align_of_gt_0);;

(* Valid pointer address for a pointee type *)
let valid_addr_def = define `
    valid_addr (p : addr, ty : ctype) = (
        let al = align_of ty in
        let sz = size_of ty in
        ((p == &0) (mod al)) /\ (p + sz < tptr_max)
    )`;;

(* Valid value for a C scalar type *)
let valid_value_def = define `
    valid_value (v : int, ty : ctype) = (
        match ty with
        | Tchar -> (v >= tchar_min) /\ (v <= tchar_max)
        | Tuchar -> (v >= tuchar_min) /\ (v <= tuchar_max)
        | Tshort -> (v >= tshort_min) /\ (v <= tshort_max)
        | Tushort -> (v >= tushort_min) /\ (v <= tushort_max)
        | Tint -> (v >= tint_min) /\ (v <= tint_max)
        | Tuint -> (v >= tuint_min) /\ (v <= tuint_max)
        | Tint64 -> (v >= tint64_min) /\ (v <= tint64_max)
        | Tuint64 -> (v >= tuint64_min) /\ (v <= tuint64_max)
        | Tptr -> (v >= tptr_min) /\ (v <= tptr_max)
    )`;;

(* Axiomatize separation logic proposition type and operators *)
let () =
    new_type ("hprop", 0);

    new_type_abbrev ("hlist", `:hprop list`);

    new_constant ("hentail", `:hprop -> hprop -> bool`);
    new_constant ("hpure", `:bool -> hprop`);
    new_constant ("htrue", `:hprop`);
    new_constant ("hfalse", `:hprop`);
    new_constant ("hand", `:hprop -> hprop -> hprop`);
    new_constant ("hor", `:hprop -> hprop -> hprop`);
    new_constant ("himpl", `:hprop -> hprop -> hprop`);
    new_constant ("hexists", `:(A -> hprop) -> hprop`);
    new_constant ("hforall", `:(A -> hprop) -> hprop`);
    new_constant ("hemp", `:hprop`);
    new_constant ("hsep", `:hprop -> hprop -> hprop`);
    new_constant ("hwand", `:hprop -> hprop -> hprop`);
    new_constant ("hiter", `:hlist -> hprop`);

    new_constant ("hfact", `:bool -> hprop`);
    new_constant ("byte_at", `:addr # int -> hprop`);
    new_constant ("data_at", `:addr # ctype # int -> hprop`);
    new_constant ("undef_data_at", `:addr # ctype -> hprop`);
    new_constant ("malloc_at", `:addr # int -> hprop`)
;;

(* Notations for parsing and printing *)
let () =
    override_interface ("|-", `hentail`);
    (* hequiv extensionality by default *)
    override_interface ("-|-", `(=):hprop->hprop->bool`);
    override_interface ("pure", `hpure`);
    override_interface ("fact", `hfact`);
    override_interface ("emp", `hemp`);
    override_interface ("**", `hsep`);
    override_interface ("-*", `hwand`)
;;

let () = 
    parse_as_infix ("|-", (2, "right"));
    parse_as_infix ("-|-", (2, "right"));
    parse_as_infix ("-*", (4, "right"));
    parse_as_infix ("||", (6, "right"));
    parse_as_infix ("&&", (8, "right"));
    parse_as_infix ("**", (8, "right"))
;;

(* Overloadables *)
let () =    
    make_overloadable "true" `:A`;
    make_overloadable "false" `:A`;
    make_overloadable "||" `:A -> A -> A`;
    make_overloadable "&&" `:A -> A -> A`;
    make_overloadable "==>" `:A -> A -> A`;
    make_overloadable "exists" `:(A -> B) -> B`;
    make_overloadable "forall" `:(A -> B) -> B`;
    
    overload_interface("true", `true:bool`);
    overload_interface("true", `htrue:hprop`);
        
    overload_interface("false", `false:bool`);
    overload_interface("false", `hfalse:hprop`);

    overload_interface("||", `(\/):bool -> bool -> bool`);
    overload_interface("||", `hor:hprop -> hprop -> hprop`);
    
    overload_interface("&&", `(/\):bool -> bool -> bool`);
    overload_interface("&&", `hand:hprop -> hprop -> hprop`);

    overload_interface("==>", `(==>):bool -> bool -> bool`);
    overload_interface("==>", `himpl:hprop -> hprop -> hprop`);

    
    overload_interface("forall", `(!):(A -> bool) -> bool`);
    overload_interface("forall", `hforall:(A -> hprop) -> hprop`);
    
    overload_interface("exists", `(?):(A -> bool) -> bool`);
    overload_interface("exists", `hexists:(A -> hprop) -> hprop`)
;;

let () =
    the_implicit_types := [
        "p", `:bool`;
        "hp", `:hprop`;
        "hp1", `:hprop`;
        "hp2", `:hprop`;
        "hp3", `:hprop`;
        "hp1'", `:hprop`;
        "hp2'", `:hprop`;
        "hp3'", `:hprop`;
        "hpA", `:A -> hprop`;
        "hpA1", `:A -> hprop`;
        "hpA2", `:A -> hprop`;
        "hpA3", `:A -> hprop`;
    ];
    do_list add_to_database [
        (* separation logic entailment defines an order on hprop *)
        ("hentail_refl", new_axiom `!hp. hp |- hp`);
        ("hentail_trans", new_axiom `!hp1 hp2 hp3. (hp1 |- hp2) ==> (hp2 |- hp3) ==> (hp1 |- hp3)`);
        ("hentail_antisym", new_axiom `!hp1 hp2. (hp1 |- hp2) ==> (hp2 |- hp1) ==> (hp1 -|- hp2)`);
        
        (* (hsep, hemp) form a commutative monoid *)
        ("hsep_assoc", new_axiom `!hp1 hp2 hp3. ((hp1 ** hp2) ** hp3) -|- (hp1 ** (hp2 ** hp3))`);
        ("hsep_comm", new_axiom `!hp1 hp2. (hp1 ** hp2) -|- (hp2 ** hp1)`);
        ("hsep_hemp_left", new_axiom `!hp. (emp ** hp) -|- hp`);
        ("hsep_hemp_right", new_axiom `!hp. (hp ** emp) -|- hp`);

        (* hsep cancellation rules *)
        ("hsep_cancel_left", new_axiom `!hp2 hp2' hp1. (hp2 |- hp2') ==> (hp1 ** hp2 |- hp1 ** hp2')`);
        ("hsep_cancel_right", new_axiom `!hp1 hp1' hp2. (hp1 |- hp1') ==> (hp1 ** hp2 |- hp1' ** hp2)`);
        ("hsep_monotone", new_axiom `!hp1 hp1' hp2 hp2'. (hp1 |- hp1') ==> (hp2 |- hp2') ==> (hp1 ** hp2 |- hp1' ** hp2')`);
                
        (* quantifier extraction rules; note the reverse side for forall-extraction doesn't hold *)
        ("hsep_hexists_left", new_axiom `!hpA hp. (hexists x : A. hpA x) ** hp |- hexists x : A. (hpA x ** hp)`);
        ("hsep_hexists_right", new_axiom `!hp hpA. hp ** (hexists x : A. hpA x) |- hexists x : A. (hp ** hpA x)`);
        ("hsep_hforall_left", new_axiom `!hpA hp. (hforall x : A. hpA x) ** hp |- hforall x : A. (hpA x ** hp)`);
        ("hsep_hforall_right", new_axiom `!hp hpA. hp ** (hforall x : A. hpA x) |- hforall x : A. (hp ** hpA x)`);
        ("hexists_left", new_axiom `!hpA hp. (!x : A. hpA x |- hp) ==> (hexists x : A. hpA x) |- hp`);
        
        (* definition of hfact (requires an empty heap) and derived properties *)
        ("hfact_def", new_axiom `!p. hfact p = (hpure p && emp)`);
        ("hfact_hpure_left", new_axiom `!p hp. hfact p ** hp -|- hpure p && hp`);
        ("hfact_hpure_right", new_axiom `!p hp. hp ** hfact p -|- hp && hpure p`);

        (* definition of data_at *)
        (* ("data_at_def", new_axiom `!p hp. data_at p hp = (hpure p ** hp)`); *)

        (* hpure *)
        ("hpure_intro", new_axiom`!p. p ==> !hp. (hp |- hpure p ** hp)`);
        ("hpure_elim", new_axiom`!p hp. (hp |- hpure p) ==> p`);
        
        ("hand_comm", new_axiom`!hp1 hp2. (hp1 ** hp2) = (hp2 ** hp1)`);
        ("hor_comm", new_axiom`!hp1 hp2. (hp1 || hp2) = (hp2 || hp1)`);
        ("hand_assoc", new_axiom`!hp1 hp2 hp3. ((hp1 ** hp2) ** hp3) = (hp1 ** (hp2 ** hp3))`);
        ("hor_assoc", new_axiom`!hp1 hp2 hp3. ((hp1 || hp2) || hp3) = (hp1 || (hp2 || hp3))`);
        ("hand_emp_left", new_axiom`!hp. (emp ** hp) = hp`);
        ("hor_emp_left", new_axiom`!hp. (emp || hp) = hp`);
        ("hand_emp_right", new_axiom`!hp. (hp ** emp) = hp`);
        ("hor_emp_right", new_axiom`!hp. (hp || emp) = hp`)
    ]
;;

assoc "hand_emp_left" !theorems;;



(* merge bits from a list of bytes (big-endian) and transform to the signed or unsigned integer *)
