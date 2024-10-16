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

(* Get a theorem from the search database *)
let get_theorem name =
    assoc name !theorems
;;

(* Print variables with types *)
let print_typed_var fmt tm =
    let s, ty = dest_var tm in
    pp_print_string fmt ("(" ^ s ^ ":" ^ string_of_type ty ^ ")")
;;

(* Personal preferences and useful information *)
let set_preference debug =
    prioritize_int ();
    type_invention_warning := true;
    install_user_printer("print_typed_var", print_typed_var);
    if debug then begin
        delete_user_printer "print_typed_var";
        reduce_interface ("true", `T:bool`);
        reduce_interface ("false", `F:bool`);
        reduce_interface ("&&", `(/\):bool->bool->bool`);
        reduce_interface ("||", `(\/):bool->bool->bool`);
        reduce_interface ("forall", `(!):(A->bool)->bool`);
        reduce_interface ("exists", `(?):(A->bool)->bool`);
    end
;;

(* Unset multiple subgoals (a lexer option handled by preprocessor) *)
unset_then_multiple_subgoals;;

(* Helper function for uncurrying; C* usually exports an uncurried interfaces (except for operators) *)
let uncurry_def = new_definition
    `uncurry (f : A -> B -> C) = \(x,y). f x y`
;;

(* Commonly used synonyms *)
new_type_abbrev ("Z", `:int`);;
new_type_abbrev ("addr", `:int`);;
new_type_abbrev ("ilist", `:int list`);;

(* Get the address of a variable/R-expression in C (represented as a string currently) *)
new_constant ("addr_of", `:string -> addr`);;

(* Overload the previous interface ("&", `int_of_num`) *)
the_overload_skeletons := update_assoc ("&", `:A -> int`) !the_overload_skeletons;; (* Warning: is this safe? *)
overload_interface ("&", `addr_of`);;

(* Overload the notation `==` for equality *)
make_overloadable "==" `:A -> A -> B`;;
overload_interface("==", `(==):A -> A -> (A->A->bool) -> bool`);; (* Warning: the notation `==` is used for congruence relations in `int.ml` *)
overload_interface("==", `(=):A -> A -> bool`);;

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
new_type ("hprop", 0);;
new_type_abbrev ("hlist", `:hprop list`);;

(* Implicit types for variables in the following axioms *)
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
];;

(* Notations for parsing and printing separation logic assertions *)
parse_as_infix ("|-", (2, "right"));;
parse_as_infix ("-|-", (2, "right"));;
parse_as_infix ("-*", (4, "right"));;
parse_as_infix ("||", (6, "right"));;
parse_as_infix ("&&", (8, "right"));;
parse_as_infix ("**", (8, "right"));;

override_interface ("|-", `hentail : hprop -> hprop -> bool`);;
override_interface ("-|-", `(=):hprop->hprop->bool`);; (* hequiv extensionality by default *)
override_interface ("pure", `hpure : bool -> hprop`);;
override_interface ("fact", `hfact : bool -> hprop`);;
override_interface ("emp", `hemp : hprop`);;
override_interface ("**", `hsep : hprop -> hprop -> hprop`);;
override_interface ("-*", `hwand : hprop -> hprop -> hprop`);;

make_overloadable "true" `:A`;;
make_overloadable "false" `:A`;;
make_overloadable "||" `:A -> A -> A`;;
make_overloadable "&&" `:A -> A -> A`;;
make_overloadable "==>" `:A -> A -> A`;;
make_overloadable "exists" `:(A -> B) -> B`;;
make_overloadable "forall" `:(A -> B) -> B`;;

overload_interface("true", `true:bool`);;
overload_interface("true", `htrue:hprop`);;
overload_interface("false", `false:bool`);;
overload_interface("false", `hfalse:hprop`);;
overload_interface("||", `(\/):bool -> bool -> bool`);;
overload_interface("||", `hor:hprop -> hprop -> hprop`);;
overload_interface("&&", `(/\):bool -> bool -> bool`);;
overload_interface("&&", `hand:hprop -> hprop -> hprop`);;
overload_interface("==>", `(==>):bool -> bool -> bool`);;
overload_interface("==>", `himpl:hprop -> hprop -> hprop`);;
overload_interface("forall", `(!):(A -> bool) -> bool`);;
overload_interface("forall", `hforall:(A -> hprop) -> hprop`);;
overload_interface("exists", `(?):(A -> bool) -> bool`);;
overload_interface("exists", `hexists:(A -> hprop) -> hprop`);;

new_constant ("hentail", `:hprop -> hprop -> bool`);;

new_constant ("hemp", `:hprop`);;
new_constant ("hsep", `:hprop -> hprop -> hprop`);;
new_constant ("hwand", `:hprop -> hprop -> hprop`);;

new_constant ("htrue", `:hprop`);;
new_constant ("hfalse", `:hprop`);;
new_constant ("hand", `:hprop -> hprop -> hprop`);;
new_constant ("hor", `:hprop -> hprop -> hprop`);;
new_constant ("himpl", `:hprop -> hprop -> hprop`);;
new_constant ("hexists", `:(A -> hprop) -> hprop`);;
new_constant ("hforall", `:(A -> hprop) -> hprop`);;

new_constant ("hpure", `:bool -> hprop`);;
new_constant ("hfact", `:bool -> hprop`);;

new_constant ("hiter", `:hlist -> hprop`);;
new_constant ("byte_at", `:addr # int -> hprop`);;
new_constant ("data_at", `:addr # ctype # int -> hprop`);;
new_constant ("undef_data_at", `:addr # ctype -> hprop`);;
new_constant ("malloc_at", `:addr # int -> hprop`);;
new_constant ("array_at", `:addr # ctype # ilist -> hprop`);;
new_constant ("undef_array_at", `:addr # ctype # int -> hprop`);;

(* Debug mode *)
set_preference true;;

(* separation logic entailment defines an order on hprop *)
do_list add_to_database [
    ("hentail_refl", new_axiom `!hp. hp |- hp`);
    ("hentail_trans", new_axiom `!hp1 hp2 hp3. (hp1 |- hp2) ==> (hp2 |- hp3) ==> (hp1 |- hp3)`);
    ("hentail_antisym", new_axiom `!hp1 hp2. (hp1 |- hp2) ==> (hp2 |- hp1) ==> (hp1 -|- hp2)`);
];;

(* (hsep, hemp) form a commutative monoid *)
do_list add_to_database [
    ("hsep_assoc", new_axiom `!hp1 hp2 hp3. (hp1 ** hp2) ** hp3 -|- hp1 ** (hp2 ** hp3)`);
    ("hsep_comm", new_axiom `!hp1 hp2. hp1 ** hp2 -|- hp2 ** hp1`);
    ("hsep_hemp_left", new_axiom `!hp. emp ** hp -|- hp`);
    ("hsep_hemp_right", new_axiom `!hp. hp ** emp -|- hp`);
];;

(* hwand-hsep adjoint law *)
do_list add_to_database [
    ("hwand_hsep_adjoint", new_axiom `!hp1 hp2 hp3. (hp1 ** hp2 |- hp3) <=> (hp1 |- hp2 -* hp3)`);
];;

(* hsep "frame" or cancellation rules *)
do_list add_to_database [
    ("hsep_cancel_left", new_axiom `!hp2 hp2' hp1. (hp2 |- hp2') ==> (hp1 ** hp2 |- hp1 ** hp2')`);
    ("hsep_cancel_right", new_axiom `!hp1 hp1' hp2. (hp1 |- hp1') ==> (hp1 ** hp2 |- hp1' ** hp2)`);
    ("hsep_monotone", new_axiom `!hp1 hp1' hp2 hp2'. (hp1 |- hp1') ==> (hp2 |- hp2') ==> (hp1 ** hp2 |- hp1' ** hp2')`);
];;

(* htrue hfalse definitions *)
do_list add_to_database [
    ("htrue_def", new_axiom `!hp. htrue = (hpure T)`);
    ("hfalse_def", new_axiom `!hp. hfalse = (hpure F)`);
];;

(* natural deduction of ordinary higher-order logic *)
do_list add_to_database [
    ("htrue_intro", new_axiom `!hp. hp |- htrue`);
    ("hfalse_elim", new_axiom `!hp. hfalse |- hp`);
    ("hand_intro", new_axiom `!hp1 hp2 hp3. (hp1 |- hp2) ==> (hp1 |- hp3) ==> (hp1 |- hp2 && hp3)`);
    ("hand_elim1", new_axiom `!hp1 hp2. (hp1 && hp2 |- hp1)`);
    ("hand_elim2", new_axiom `!hp1 hp2. (hp1 && hp2 |- hp2)`);
    ("hor_intro1", new_axiom `!hp1 hp2. (hp1 |- hp1 || hp2)`);
    ("hor_intro2", new_axiom `!hp1 hp2. (hp2 |- hp1 || hp2)`);
    ("hor_elim", new_axiom `!hp1 hp2 hp3. (hp1 |- hp3) ==> (hp2 |- hp3) ==> (hp1 || hp2 |- hp3)`);
    ("himpl_hand_adjoint", new_axiom `!hp1 hp2 hp3. (hp1 && hp2 |- hp3) <=> (hp1 |- hp2 ==> hp3)`);
    ("hexists_intro", new_axiom `!hp hpA (x : A). (hp |- hpA x) ==> (hp |- (exists x : A. hpA x))`);
    ("hexists_elim", new_axiom `!hp hpA. (!x : A. hpA x |- hp) ==> ((exists x : A. hpA x) |- hp)`);
    ("hforall_intro", new_axiom `!hp hpA. (!x : A. hp |- hpA x) ==> (hp |- (forall x : A. hpA x))`);
    ("hforall_elim", new_axiom `!hp hpA (x : A). (hpA x |- hp) ==> ((forall x : A. hpA x) |- hp)`);
];;

(* hpure intro-and-elim rules *)
do_list add_to_database [
    ("hpure_intro", new_axiom `!p hp. p ==> (hp |- hpure p)`);
    ("hpure_elim", new_axiom `!p hp. (p ==> (htrue |- hp)) ==> (hpure p |- hp)`);
];;

(* hpure extraction rules *)
do_list add_to_database [
    ("hsep_hpure_left", new_axiom `!p hp1 hp2. (hpure p && hp1) ** hp2 -|- hpure p && (hp1 ** hp2)`);
    ("hsep_hpure_right", new_axiom `!p hp1 hp2. hp1 ** (hpure p && hp2) -|- hpure p && (hp1 ** hp2)`);
];;

(* hfact-hpure relation ship*)
do_list add_to_database [
    ("hfact_def", new_axiom `!p hp. hfact p = (hpure p && emp)`);
    ("hfact_hpure", new_axiom `!p hp. hfact p ** hp -|- hpure p && hp`);
];;

(* quantifier extraction rules; note the reverse side for forall-extraction doesn't hold *)
do_list add_to_database [
    ("hsep_hexists_left", new_axiom `!hpA hp. (exists x : A. hpA x) ** hp -|- exists x : A. (hpA x ** hp)`);
    ("hsep_hexists_right", new_axiom `!hp hpA. hp ** (exists x : A. hpA x) -|- exists x : A. (hp ** hpA x)`);
    ("hsep_hforall_left", new_axiom `!hpA hp. (forall x : A. hpA x) ** hp |- forall x : A. (hpA x ** hp)`);
    ("hsep_hforall_right", new_axiom `!hp hpA. hp ** (forall x : A. hpA x) |- forall x : A. (hp ** hpA x)`);
    ("hand_hexists_left", new_axiom `!hpA hp. (exists x : A. hpA x) && hp -|- exists x : A. (hpA x && hp)`);
    ("hand_hexists_right", new_axiom `!hp hpA. hp && (exists x : A. hpA x) -|- exists x : A. (hp && hpA x)`);
    ("hand_hforall_left", new_axiom `!hpA hp. (forall x : A. hpA x) && hp |- forall x : A. (hpA x && hp)`); (* Reverse side holds in HOL? (no empty type) *)
    ("hand_hforall_right", new_axiom `!hp hpA. hp && (forall x : A. hpA x) |- forall x : A. (hp && hpA x)`); (* Reverse side holds in HOL? (no empty type) *)    
];;

(* definition of data_at *)
