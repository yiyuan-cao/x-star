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
let add_to_database name thm =
    theorems := update_assoc (name, thm) !theorems;
    thm
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
    (* install_user_printer("print_typed_var", print_typed_var); *)
    if debug then begin
        type_invention_error := true;
        print_types_of_subterms := 2;
        reduce_interface ("true", `T:bool`);
        reduce_interface ("false", `F:bool`);
        reduce_interface ("&&", `(/\):bool->bool->bool`);
        reduce_interface ("||", `(\/):bool->bool->bool`);
        reduce_interface ("forall", `(!):(A->bool)->bool`);
        reduce_interface ("exists", `(?):(A->bool)->bool`);
    end
;;

set_preference false;;

(* Unset multiple subgoals (a lexer option handled by preprocessor) *)
unset_then_multiple_subgoals;;

(* Commonly used synonyms *)
new_type_abbrev ("Z", `:int`);;
new_type_abbrev ("addr", `:int`);;
new_type_abbrev ("ilist", `:int list`);;

(* exported functions *)
let ilength_def = define `ilength NIL = &0 /\ ilength (CONS (h:A) t) = &1 + ilength t`;;
add_to_database "ilength_def" ilength_def;;
let ireplicate_def = define `ireplicate (n : int, x : int) : ilist = REPLICATE (num_of_int n) x`;;
add_to_database "ireplicate_def" ireplicate_def;;

(* range of ints from lo (inclusive) to hi (exclusive) *)
let irange_def = define `irange (lo : int, hi : int) = list_of_seq (\i. lo + (&i) : int) (num_of_int (hi - lo))`;;
add_to_database "irange_def" irange_def;;

let irange0_def = define `irange0 (n : int) : ilist = list_of_seq int_of_num (num_of_int n)`;;
add_to_database "irange0_def" irange0_def;;

let irange0_to_irange = new_axiom
    `!n. n >= &0 ==> (irange0 n = irange (&0, n))`;;
add_to_database "irange0_to_irange" irange0_to_irange;;

let irange_split = new_axiom
    `!lo mid hi. (lo <= mid /\ mid <= hi) ==>
                 (irange (lo, hi) = APPEND (irange (lo, mid)) (irange (mid, hi)))`;;
add_to_database "irange_split" irange_split;;

(* Convert a list of bytes to an represented unsigned integer, with the least significant byte first (LITTLE-ENDIAN) *)
(* For example, the list [0x12; 0x34; 0x56; 0x78] represents the integer 0x78563412 *)
(* Should be a natural number if vs is a valid list of byte values (uchar) *)
let int_of_bytes_def = define `
    int_of_bytes (bs : ilist) : int = 
        ITLIST (\b n. n * (&256) + b) bs (&0)`;;
add_to_database "int_of_bytes_def" int_of_bytes_def;;

let int_of_bytes_example = prove (`int_of_bytes [&0x12; &0x34; &0x56; &0x78] = &0x78563412`,
    SIMP_TAC [int_of_bytes_def; ITLIST] THEN
    INT_ARITH_TAC
);;

(* Get the address of a variable/R-expression in C (represented as a string currently) *)
(* TODO: change to a more appropriate type for R-expressions *)
new_constant ("addr_of", `:string -> addr`);;

(* Overload the previous interface ("&", `int_of_num`) *)
the_overload_skeletons := update_assoc ("&", `:A -> int`) !the_overload_skeletons;; (* Warning: is this safe? *)
overload_interface ("&", `addr_of:string -> addr`);;

(* C scalar types *)
let ctype_induct, ctype_rec = define_type "
    ctype =
        Tchar  | Tuchar  |
        Tshort | Tushort |
        Tint   | Tuint   |
        Tint64 | Tuint64 |
                 Tptr
";;

(* TODO: add support of compound types: arrays, structs, unions *)

(* Word size in bytes *)
let word_size_def = define `word_size = &4`;;
add_to_database "word_size_def" word_size_def;;

(* Size of a C scalar type in bytes *)
let sizeof_def = define `
    sizeof ty = 
        match ty with
        | Tchar    ->  &1
        | Tuchar   ->  &1
        | Tshort   ->  &2
        | Tushort  ->  &2
        | Tint     ->  &4
        | Tuint    ->  &4
        | Tint64   ->  &8
        | Tuint64  ->  &8
        | Tptr     ->  word_size`
;;
add_to_database "sizeof_def" sizeof_def;;

(* Alignment requirement of a C scalar type *)
let align_of_def = define `
    align_of ty = 
        match ty with
        | Tchar    ->  &1
        | Tuchar   ->  &1
        | Tshort   ->  &2
        | Tushort  ->  &2
        | Tint     ->  &4
        | Tuint    ->  &4
        | Tint64   ->  min word_size (&8)
        | Tuint64  ->  min word_size (&8)
        | Tptr     ->  word_size`
;;
add_to_database "align_of_def" align_of_def;;

(* Minimum and maximum values of C scalar types *)
let min_of_def = define `
    min_of ty = 
        match ty with
        | Tchar    ->  --(&2 pow (num_of_int (sizeof Tchar)  - 1))
        | Tshort   ->  --(&2 pow (num_of_int (sizeof Tshort) - 1))
        | Tint     ->  --(&2 pow (num_of_int (sizeof Tint)   - 1))
        | Tint64   ->  --(&2 pow (num_of_int (sizeof Tint64) - 1))
        | Tuchar   ->  &0
        | Tushort  ->  &0
        | Tuint    ->  &0
        | Tuint64  ->  &0
        | Tptr     ->  &0`
;;
add_to_database "min_of_def" min_of_def;;

let max_of_def = define `
    max_of ty = 
        match ty with
        | Tchar    ->  &2 pow (num_of_int (sizeof Tchar)  - 1) - (&1)
        | Tshort   ->  &2 pow (num_of_int (sizeof Tshort) - 1) - (&1)
        | Tint     ->  &2 pow (num_of_int (sizeof Tint)   - 1) - (&1)
        | Tint64   ->  &2 pow (num_of_int (sizeof Tint64) - 1) - (&1)
        | Tuchar   ->  &2 pow (num_of_int (sizeof Tuchar))     - (&1)
        | Tushort  ->  &2 pow (num_of_int (sizeof Tushort))    - (&1)
        | Tuint    ->  &2 pow (num_of_int (sizeof Tuint))      - (&1)
        | Tuint64  ->  &2 pow (num_of_int (sizeof Tuint64))    - (&1)
        | Tptr     ->  &2 pow (num_of_int (sizeof Tptr))       - (&1)`
;;
add_to_database "max_of_def" max_of_def;;

(* Size of a type is positive *)
let sizeof_gt_0 = prove (
    `!ty. sizeof ty > &0`,
    MATCH_MP_TAC ctype_induct THEN
    REWRITE_TAC [word_size_def; sizeof_def] THEN
    REPEAT STRIP_TAC THENL
    replicate INT_ARITH_TAC 9
);;
add_to_database "sizeof_gt_0" sizeof_gt_0;;

(* Alignment of a type is positive *)
let align_of_gt_0 = prove (
    `!ty. align_of ty > &0`,
    MATCH_MP_TAC ctype_induct THEN
    REWRITE_TAC [word_size_def; align_of_def] THEN
    REPEAT STRIP_TAC THENL
    replicate INT_ARITH_TAC 9
);;
add_to_database "align_of_gt_0" align_of_gt_0;;

(* Valid pointer address for a pointee type *)
let valid_addr_def = define `
    valid_addr (p : addr, ty : ctype) = (
        let al = align_of ty in
        let sz = sizeof ty in
        ((p == &0) (mod al)) /\ (p + sz < max_of Tptr)
    )`;;
add_to_database "valid_addr_def" valid_addr_def;;

(* Valid value for a C scalar type *)
let valid_value_def = define `
    valid_value (v : int, ty : ctype) =
        ((min_of ty <= v) /\ (v <= max_of ty))
`;;
add_to_database "valid_value_def" valid_value_def;;

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
    "hps", `:hlist`;
    "hps1", `:hlist`;
    "hps2", `:hlist`;
];;

(* Overload the notation `==` for equality *)
make_overloadable "==" `:A -> A -> B`;;
overload_interface("==", `(==):A -> A -> (A->A->bool) -> bool`);; (* Warning: the notation `==` is used for congruence relations in `int.ml` *)
overload_interface("==", `(=):A -> A -> bool`);;
override_interface("<=>", `(=):bool->bool->bool`);;

(* arithmetic operators *)
override_interface ("/", `(div):int->int->int`);;

(* Notations for parsing and printing separation logic assertions *)
parse_as_infix ("|--", (2, "right"));;
parse_as_infix ("-|-", (2, "right"));;
parse_as_infix ("-*", (4, "right"));;
parse_as_infix ("-->", (4, "right"));;
parse_as_infix ("||", (6, "right"));;
parse_as_infix ("&&", (8, "right"));;
parse_as_infix ("**", (8, "right"));;

override_interface ("|--", `hentail : hprop -> hprop -> bool`);;
override_interface ("-|-", `(=):hprop->hprop->bool`);; (* hequiv extensionality by default *)
override_interface ("pure", `hpure : bool -> hprop`);;
override_interface ("fact", `hfact : bool -> hprop`);;
override_interface ("emp", `hemp : hprop`);;
override_interface ("**", `hsep : hprop -> hprop -> hprop`);;
override_interface ("-*", `hwand : hprop -> hprop -> hprop`);;
override_interface ("-->", `himpl : hprop -> hprop -> hprop`);;

(* TODO: install user-printer instead of overloading! *)
make_overloadable "true" `:A`;;
make_overloadable "false" `:A`;;
make_overloadable "||" `:A -> A -> A`;;
make_overloadable "&&" `:A -> A -> A`;;
make_overloadable "exists" `:(A -> B) -> B`;;
make_overloadable "forall" `:(A -> B) -> B`;;

overload_interface("true", `T:bool`);;
overload_interface("true", `htrue:hprop`);;
overload_interface("false", `F:bool`);;
overload_interface("false", `hfalse:hprop`);;
overload_interface("||", `(\/):bool -> bool -> bool`);;
overload_interface("||", `hor:hprop -> hprop -> hprop`);;
overload_interface("&&", `(/\):bool -> bool -> bool`);;
overload_interface("&&", `hand:hprop -> hprop -> hprop`);;
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
new_constant ("hiter_irange", `:(int -> hprop) # int # int -> hprop`);; (* fprop, lo (inclusive), hi (exclusive) *)
new_constant ("hiter_irange0", `:(int -> hprop) # int -> hprop`);; (* fprop, 0 (inclusive), n (exclusive) *)

new_constant ("byte_at", `:addr # int -> hprop`);;
new_constant ("bytes_at", `:addr # ilist -> hprop`);;

new_constant ("data_at", `:addr # ctype # int -> hprop`);;
new_constant ("undef_data_at", `:addr # ctype -> hprop`);;

new_constant ("cell_at", `:addr # ctype # int # int -> hprop`);;    (* data_at with offset index; inputs: base, elem type, index, represented integer *)
new_constant ("undef_cell_at", `:addr # ctype # int -> hprop`);;
new_constant ("slice_at", `:addr # ctype # int # ilist -> hprop`);; (* array_at with offset index; inputs: base, elem type, start index, list of represented integers *)
new_constant ("undef_slice_at", `:addr # ctype # int # int -> hprop`);;
new_constant ("array_at", `:addr # ctype # ilist -> hprop`);;
new_constant ("undef_array_at", `:addr # ctype # int -> hprop`);;

new_constant ("malloc_at", `:addr # int -> hprop`);;                 (* malloc_at base, size of malloced region *)

(* separation logic entailment defines an order on hprop *)
let hentail_refl = new_axiom `!hp. hp |-- hp`;;
add_to_database "hentail_refl" hentail_refl;;

let hentail_trans = new_axiom `!hp1 hp2 hp3. (hp1 |-- hp2) ==> (hp2 |-- hp3) ==> (hp1 |-- hp3)`;;
add_to_database "hentail_trans" hentail_trans;;

let hentail_antisym = new_axiom `!hp1 hp2. (hp1 |-- hp2) ==> (hp2 |-- hp1) ==> (hp1 -|- hp2)`;;
add_to_database "hentail_antisym" hentail_antisym;;

(* (hsep, hemp) form a commutative monoid *)
let hsep_assoc = new_axiom `!hp1 hp2 hp3. (hp1 ** hp2) ** hp3 -|- hp1 ** (hp2 ** hp3)`;;
add_to_database "hsep_assoc" hsep_assoc;;

let hsep_comm = new_axiom `!hp1 hp2. hp1 ** hp2 -|- hp2 ** hp1`;;
add_to_database "hsep_comm" hsep_comm;;

let hsep_hemp_left = new_axiom `!hp. emp ** hp -|- hp`;;
add_to_database "hsep_hemp_left" hsep_hemp_left;;

let hsep_hemp_right = new_axiom `!hp. hp ** emp -|- hp`;;
add_to_database "hsep_hemp_right" hsep_hemp_right;;

(* hwand-hsep adjoint law *)
let hwand_hsep_adjoint = new_axiom `!hp1 hp2 hp3. (hp1 ** hp2 |-- hp3) <=> (hp1 |-- hp2 -* hp3)`;;
add_to_database "hwand_hsep_adjoint" hwand_hsep_adjoint;;

(* hsep "frame" or cancellation rules *)
let hsep_cancel_left = new_axiom `!hp2 hp2' hp1. (hp2 |-- hp2') ==> (hp1 ** hp2 |-- hp1 ** hp2')`;;
add_to_database "hsep_cancel_left" hsep_cancel_left;;

let hsep_cancel_right = new_axiom `!hp1 hp1' hp2. (hp1 |-- hp1') ==> (hp1 ** hp2 |-- hp1' ** hp2)`;;
add_to_database "hsep_cancel_right" hsep_cancel_right;;

let hsep_monotone = new_axiom `!hp1 hp1' hp2 hp2'. (hp1 |-- hp1') ==> (hp2 |-- hp2') ==> (hp1 ** hp2 |-- hp1' ** hp2')`;;
add_to_database "hsep_monotone" hsep_monotone;;

(* htrue hfalse definitions *)
let htrue_def = new_axiom `!hp. htrue = (hpure T)`;;
add_to_database "htrue_def" htrue_def;;

let hfalse_def = new_axiom `!hp. hfalse = (hpure F)`;;
add_to_database "hfalse_def" hfalse_def;;

(* natural deduction of ordinary higher-order logic connectives *)
let htrue_intro = new_axiom `!hp. hp |-- htrue`;;
add_to_database "htrue_intro" htrue_intro;;

let hfalse_elim = new_axiom `!hp. hfalse |-- hp`;;
add_to_database "hfalse_elim" hfalse_elim;;

let hfalse_absorb_left = new_axiom `!hp. (hfact F) ** hp -|- (hfact F)`;;
add_to_database "hfalse_absorb_left" hfalse_absorb_left;;

let hfalse_absorb_right = new_axiom `!hp. hp ** (hfact F) -|- (hfact F)`;;
add_to_database "hfalse_absorb_right" hfalse_absorb_right;;

let hand_intro = new_axiom `!hp1 hp2 hp3. (hp1 |-- hp2) ==> (hp1 |-- hp3) ==> (hp1 |-- hp2 && hp3)`;;
add_to_database "hand_intro" hand_intro;;

let hand_elim1 = new_axiom `!hp1 hp2. (hp1 && hp2 |-- hp1)`;;
add_to_database "hand_elim1" hand_elim1;;

let hand_elim2 = new_axiom `!hp1 hp2. (hp1 && hp2 |-- hp2)`;;
add_to_database "hand_elim2" hand_elim2;;

let hor_intro1 = new_axiom `!hp1 hp2. (hp1 |-- hp1 || hp2)`;;
add_to_database "hor_intro1" hor_intro1;;

let hor_intro2 = new_axiom `!hp1 hp2. (hp2 |-- hp1 || hp2)`;;
add_to_database "hor_intro2" hor_intro2;;

let hor_elim = new_axiom `!hp1 hp2 hp3. (hp1 |-- hp3) ==> (hp2 |-- hp3) ==> (hp1 || hp2 |-- hp3)`;;
add_to_database "hor_elim" hor_elim;;

let himpl_hand_adjoint = new_axiom `!hp1 hp2 hp3. (hp1 && hp2 |-- hp3) <=> (hp1 |-- hp2 --> hp3)`;;
add_to_database "himpl_hand_adjoint" himpl_hand_adjoint;;

let hexists_intro = new_axiom `!hp hpA (x : A). (hp |-- hpA x) ==> (hp |-- (exists x : A. hpA x))`;; (* Instantiation on the right *)
add_to_database "hexists_intro" hexists_intro;;

let hexists_elim = new_axiom `!hp hpA. (!x : A. hpA x |-- hp) ==> ((exists x : A. hpA x) |-- hp)`;; (* Used for extraction *)
add_to_database "hexists_elim" hexists_elim;;

let hforall_intro = new_axiom `!hp hpA. (!x : A. hp |-- hpA x) ==> (hp |-- (forall x : A. hpA x))`;; (* Used for extraction *)
add_to_database "hforall_intro" hforall_intro;;

let hforall_elim = new_axiom `!hp hpA (x : A). (hpA x |-- hp) ==> ((forall x : A. hpA x) |-- hp)`;; (* Instantiation on the left *)
add_to_database "hforall_elim" hforall_elim;;

(* hpure intro-and-elim rules *)
let hpure_intro = new_axiom `!p hp1 hp2. p ==> (hp1 |-- hp2) ==> (hp1 |-- hpure p && hp2)`;; (* Add pure fact to the right *)
add_to_database "hpure_intro" hpure_intro;;

let hpure_elim = new_axiom `!p hp1 hp2. (p ==> (hp1 |-- hp2)) ==> (hpure p && hp1 |-- hp2)`;; (* Extraction of pure fact to the higher-order logic context on the left *)
add_to_database "hpure_elim" hpure_elim;;

(* hpure extraction rules *)
let hand_assoc = new_axiom `!hp1 hp2 hp3. (hp1 && hp2) && hp3 -|- hp1 && (hp2 && hp3)`;;
add_to_database "hand_assoc" hand_assoc;;

let hand_comm = new_axiom `!hp1 hp2. hp1 && hp2 -|- hp2 && hp1`;;
add_to_database "hand_comm" hand_comm;;

let hsep_hpure_left = new_axiom `!p hp1 hp2. (hpure p && hp1) ** hp2 -|- hpure p && (hp1 ** hp2)`;;
add_to_database "hsep_hpure_left" hsep_hpure_left;;

let hsep_hpure_right = new_axiom `!p hp1 hp2. hp1 ** (hpure p && hp2) -|- hpure p && (hp1 ** hp2)`;;
add_to_database "hsep_hpure_right" hsep_hpure_right;;

(* hfact-hpure relation ship; can also use hfact to do hpure extraction *)
let hfact_def = new_axiom `!p hp. hfact p = (hpure p && emp)`;;
add_to_database "hfact_def" hfact_def;;

let hfact_hpure = new_axiom `!p hp. hfact p ** hp -|- hpure p && hp`;;
add_to_database "hfact_hpure" hfact_hpure;;

(* hfact intro-and-elim rules *)
let hfact_intro = new_axiom `!p hp1 hp2. p ==> (hp1 |-- hp2) ==> (hp1 |-- hfact p ** hp2)`;;
add_to_database "hfact_intro" hfact_intro;;

let hfact_elim = new_axiom `!p hp1 hp2. (p ==> (hp1 |-- hp2)) ==> (hfact p ** hp1 |-- hp2)`;;
add_to_database "hfact_elim" hfact_elim;;

let hfact_dup = new_axiom `!p. hfact p |-- hfact p ** hfact p`;;
add_to_database "hfact_dup" hfact_dup;;

(* hfact extraction rules *)
let hsep_hfact_left = new_axiom `!p hp1 hp2. (hfact p ** hp1) ** hp2 -|- hfact p ** (hp1 ** hp2)`;;
add_to_database "hsep_hfact_left" hsep_hfact_left;;

let hsep_hfact_right = new_axiom `!p hp1 hp2. hp1 ** (hfact p ** hp2) -|- hfact p ** (hp1 ** hp2)`;;
add_to_database "hsep_hfact_right" hsep_hfact_right;;

(* quantifier extraction rules *)
let hsep_hexists_left = new_axiom `!hpA hp. (exists x : A. hpA x) ** hp -|- exists x : A. (hpA x ** hp)`;;
add_to_database "hsep_hexists_left" hsep_hexists_left;;

let hsep_hexists_right = new_axiom `!hp hpA. hp ** (exists x : A. hpA x) -|- exists x : A. (hp ** hpA x)`;;
add_to_database "hsep_hexists_right" hsep_hexists_right;;

let hsep_hforall_left = new_axiom `!hpA hp. (forall x : A. hpA x) ** hp |-- forall x : A. (hpA x ** hp)`;; (* Note the reverse side for forall-extraction doesn't hold *)
add_to_database "hsep_hforall_left" hsep_hforall_left;;

let hsep_hforall_right = new_axiom `!hp hpA. hp ** (forall x : A. hpA x) |-- forall x : A. (hp ** hpA x)`;; (* Note the reverse side for forall-extraction doesn't hold *)
add_to_database "hsep_hforall_right" hsep_hforall_right;;

let hand_hexists_left = new_axiom `!hpA hp. (exists x : A. hpA x) && hp -|- exists x : A. (hpA x && hp)`;;
add_to_database "hand_hexists_left" hand_hexists_left;;

let hand_hexists_right = new_axiom `!hp hpA. hp && (exists x : A. hpA x) -|- exists x : A. (hp && hpA x)`;;
add_to_database "hand_hexists_right" hand_hexists_right;;

let hand_hforall_left = new_axiom `!hpA hp. (forall x : A. hpA x) && hp |-- forall x : A. (hpA x && hp)`;; (* Reverse side holds in HOL? (no empty type) *)
add_to_database "hand_hforall_left" hand_hforall_left;;

let hand_hforall_right = new_axiom `!hp hpA. hp && (forall x : A. hpA x) |-- forall x : A. (hp && hpA x)`;; (* Reverse side holds in HOL? (no empty type) *)
add_to_database "hand_hforall_right" hand_hforall_right;;


(* Other monotonicity rules; used for constructing entailments under quantifiers or operators *)
let hexists_monotone = new_axiom `!hpA hpA'. (!x:A. hpA x |-- hpA' x) ==> ((exists x:A. hpA x) |-- (exists x:A. hpA' x))`;;
add_to_database "hexists_monotone" hexists_monotone;;

let hforall_monotone = new_axiom `!hpA hpA'. (!x:A. hpA x |-- hpA' x) ==> ((forall x:A. hpA x) |-- (forall x:A. hpA' x))`;;
add_to_database "hforall_monotone" hforall_monotone;;

let hand_monotone = new_axiom `!hp1 hp1' hp2 hp2'. (hp1 |-- hp1') ==> (hp2 |-- hp2') ==> (hp1 && hp2 |-- hp1' && hp2')`;;
add_to_database "hand_monotone" hand_monotone;;

let hor_monotone = new_axiom `!hp1 hp1' hp2 hp2'. (hp1 |-- hp1') ==> (hp2 |-- hp2') ==> (hp1 || hp2 |-- hp1' || hp2')`;;
add_to_database "hor_monotone" hor_monotone;;

(* definition of hiter, hiter_range, and their split rules *)
let hiter_def = new_axiom `hiter hps = ITLIST (**) hps emp`;; (* TODO: hiter could be defined in terms of iterate *)
add_to_database "hiter_def" hiter_def;;

let hiter_split = new_axiom `!hps1 hps2. hiter (APPEND hps1 hps2) -|- hiter hps1 ** hiter hps2`;;
add_to_database "hiter_split" hiter_split;;

let hiter_irange_def = new_axiom `hiter_irange (hpf, lo, hi) = hiter (MAP hpf (irange (lo, hi)))`;;
add_to_database "hiter_irange_def" hiter_irange_def;;

let hiter_irange0_def = new_axiom `hiter_irange0 (hpf, n) = hiter (MAP hpf (irange0 n))`;;
add_to_database "hiter_irange0_def" hiter_irange0_def;;

let hiter_irange0_to_hiter_irange = new_axiom `!hpf n. hiter_irange0 (hpf, n) -|- hiter_irange (hpf, &0, n)`;;
add_to_database "hiter_irange0_to_hiter_irange" hiter_irange0_to_hiter_irange;;

let hiter_irange_split = new_axiom `!hpf lo mid hi.
                                       (lo <= mid /\ mid <= hi) ==>
                                       (hiter_irange (hpf, lo, hi) -|- hiter_irange (hpf, lo, mid) ** hiter_irange (hpf, mid, hi))`;;
add_to_database "hiter_irange_split" hiter_irange_split;;

(* Demo: sample proof of hiter_split *)
prove (`!hps1 hps2. hiter (APPEND hps1 hps2) -|- hiter hps1 ** hiter hps2`,
    REWRITE_TAC [get_theorem "hiter_def"] THEN
    REWRITE_TAC [ITLIST_APPEND] THEN
    FIX_TAC "hps2" THEN
    MATCH_MP_TAC (list_INDUCT) THEN
    STRIP_TAC THENL
    [
        (* base case *)
        SIMP_TAC [ITLIST; get_theorem "hsep_hemp_left"];
        (* inductive case *)
        INTRO_TAC "![hp][hps];IH" THEN
        REWRITE_TAC [ITLIST; get_theorem "hsep_assoc"] THEN
        MK_COMB_TAC THENL
        [
            REFL_TAC;
            USE_THEN "IH" MATCH_ACCEPT_TAC;
        ];
    ]
);;

(* axioms of byte_at and bytes_at *)
let byte_at_dup = new_axiom `!x:addr v1 v2. byte_at (x, v1) ** byte_at (x, v2) |-- hfalse`;;
add_to_database "byte_at_dup" byte_at_dup;;

let byte_at_valid = new_axiom `!x:addr v. byte_at (x, v) |-- fact(valid_value (v, Tuchar)) ** byte_at (x, v)`;;
add_to_database "byte_at_valid" byte_at_valid;;

let bytes_at_def = new_axiom `!x:addr bs. bytes_at (x, bs) = hiter_irange0 ((\i. byte_at (x + i, EL (num_of_int i) bs)), ilength bs)`;;
add_to_database "bytes_at_def" bytes_at_def;;

(* definitions of data_at and undef_data_at *)
let data_at_def = new_axiom `!x ty v. data_at (x, ty, v) =
                                exists bs. (
                                    fact (ilength bs = sizeof ty) **
                                    fact ((v == int_of_bytes bs) (mod (&256 pow (num_of_int (sizeof ty))))) **
                                    fact (valid_value (v, ty)) **
                                    fact (valid_addr (x, ty)) **
                                    bytes_at (x, bs)
                                )`;;
add_to_database "data_at_def" data_at_def;;

let undef_data_at_def = new_axiom `!x ty. undef_data_at (x, ty) =
                                exists bs.
                                    fact (ilength bs = sizeof ty) **
                                    fact (valid_addr (x, ty)) **
                                    bytes_at (x, bs)`;;
add_to_database "undef_data_at_def" undef_data_at_def;;

let data_at_to_undef_data_at = new_axiom `!x ty. data_at (x, ty, v) |-- undef_data_at (x, ty)`;;
add_to_database "data_at_to_undef_data_at" data_at_to_undef_data_at;;

(* definition of cell_at and undef_cell_at *)
let cell_at_def = new_axiom `!x ty i v. cell_at (x, ty, i, v) = data_at (x + i * (sizeof ty), ty, v)`;;
add_to_database "cell_at_def" cell_at_def;;

let undef_cell_at_def = new_axiom `!x ty i. undef_cell_at (x, ty, i) = undef_data_at (x + i * (sizeof ty), ty)`;;
add_to_database "undef_cell_at_def" undef_cell_at_def;;

(* definition of slice_at and array_at *)
let slice_at_def = new_axiom `!x ty i vs. slice_at (x, ty, i, vs) =
                        hiter_irange0 ((\j. cell_at (x, ty, i + j, EL (num_of_int j) vs)), ilength vs)`;;
add_to_database "slice_at_def" slice_at_def;;

let undef_slice_at_def = new_axiom `!x ty i n. undef_slice_at (x, ty, i, n) =
                        hiter_irange0 ((\j. undef_cell_at (x, ty, i + j)), n)`;;
add_to_database "undef_slice_at_def" undef_slice_at_def;;

let array_at_def = new_axiom `!x ty vs. array_at (x, ty, vs) = slice_at (x, ty, &0, vs)`;;
add_to_database "array_at_def" array_at_def;;

let undef_array_at_def = new_axiom `!x ty n. undef_array_at (x, ty, n) = undef_slice_at (x, ty, &0, n)`;;
add_to_database "undef_array_at_def" undef_array_at_def;;

(* array slice split rule *)
let slice_split = new_axiom `!x ty i vs1 vs2.
            slice_at (x, ty, i, APPEND vs1 vs2) -|- slice_at (x, ty, i, vs1) ** slice_at (x, ty, i + ilength vs1, vs2)`;;
add_to_database "slice_split" slice_split;;

let array_split = new_axiom `!x ty vs1 vs2.
            array_at (x, ty, APPEND vs1 vs2) -|- array_at (x, ty, vs1) ** array_at (x + (ilength vs1) * (sizeof ty), ty, vs2)`;;
add_to_database "array_split" array_split;;

let undef_slice_split = new_axiom `!x ty i n1 n2.
            undef_slice_at (x, ty, i, n1 + n2) -|- undef_slice_at (x, ty, i, n1) ** undef_slice_at (x, ty, i + n1, n2)`;;
add_to_database "undef_slice_split" undef_slice_split;;

let undef_array_split = new_axiom `!x ty n1 n2.
            undef_array_at (x, ty, n1 + n2) -|- undef_array_at (x, ty, n1) ** undef_array_at (x + (sizeof ty) * n1, ty, n2)`;;
add_to_database "undef_array_split" undef_array_split;;

(* axioms of malloc_at *)
let malloc_at_inv = new_axiom `!x:addr n:int.
            malloc_at (x, n) |-- fact(x > &0) ** fact(n > &0) ** malloc_at (x, n)`;;
add_to_database "malloc_at_inv" malloc_at_inv;;

(* Example: hsep_hfalse_left *)
let hsep_hfalse_left = prove (`!hp. false ** hp |-- false`,
    FIX_TAC "hp" THEN
    REWRITE_TAC [hwand_hsep_adjoint] THEN
    REWRITE_TAC [hfalse_elim]
);;
add_to_database "hsep_hfalse_left" hsep_hfalse_left;;

(* Canonical form of hprop *)
let hfactize_hprop = REWRITE_CONV [GSYM hfact_hpure];;
let hpureize_hprop = REWRITE_CONV [hfact_hpure];;

let which_implies (hp_pre, th_part_entail) =
    assert (type_of hp_pre = `:hprop`);
    
    (* printf "hp_pre: \n";
    print_qterm hp_pre;
    printf "\n";

    printf "th_part_entail: \n";
    print_thm th_part_entail;
    printf "\n"; *)

    let assumps, part_entail = dest_thm th_part_entail in
    let hp_pre_part, hp_post_part = dest_binop `(|-)` part_entail in
    (* First, assumps should be pure facts that can be proved (by very simple means) from the pure facts in hp_pre *)
    assert (assumps = []); (* TODO: add support for non-empty assumps *)
    (* Then, hp_pre_part should be a subset of hp_pre *)
    let hp_pre_canon = hp_pre |> hfactize_hprop |> concl |> rhs in
    let hp_pre_part_canon = hp_pre_part |> hfactize_hprop |> concl |> rhs in

    
    printf "hp_pre: \n!";
    print_qterm hp_pre;
    printf "\n!";

    printf "hp_pre_part: \n!";
    print_qterm hp_pre_part;
    printf "\n!";

    (* Finally, then resulting theorem prove an entailment from hp_pre to hp_pre with hp_pre_part substituted by hp_post_part *)
    (* To use VST-IDE symbolic execution, the output should be in the canonical form *)
    ()
;;

(* Some derived rules needed by CStar conversion library. *)
let hsep_hfact_comm = 
  prove(`!hp p. hp ** fact p -|- fact p ** hp`,
        REWRITE_TAC[hsep_comm])
;;
add_to_database "hsep_hfact_comm" hsep_hfact_comm;;

let hfact_hpure_right = 
  prove(`!p hp. hp && hpure p -|- hfact p ** hp`,
        REWRITE_TAC[hfact_hpure; hand_comm]) 
;;
add_to_database "hfact_hpure_right" hfact_hpure_right;;

let hsep_comm_left_part = 
  prove(`!hp hp1 hp2. hp1 ** hp ** hp2 -|- hp ** hp1 ** hp2`,
          ONCE_REWRITE_TAC [GSYM hsep_assoc] THEN 
          REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN 
          ACCEPT_TAC (SPECL [`hp1`;`hp`] hsep_comm) )
;;
add_to_database "hsep_comm_left_part" hsep_comm_left_part;;

let hentail_sym_left = 
  prove(`!hp1 hp2. (hp1 -|- hp2) ==> (hp1 |-- hp2)`,
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN 
        ACCEPT_TAC (SPEC `hp2` hentail_refl))
;;
add_to_database "hentail_sym_left" hentail_sym_left;;

let hfact_elim_dup = new_axiom (* manual: [p] * hp1 |-- [p] * [p] * hp1 |-- [p] * hp2 *)
  `!p hp1 hp2. (p ==> (hp1 |-- hp2)) ==> (hfact p ** hp1 |-- hfact p ** hp2)`
;;
add_to_database "hfact_elim_dup" hfact_elim_dup;;  

(* Some derived rules for examples. *)

(* clear *)
let array_at_replicate_zero_length = new_axiom 
  `!x ty y. array_at(x, ty, replicate(&0, y)) -|- emp`
;;
add_to_database "array_at_replicate_zero_length" array_at_replicate_zero_length;;

let array_at_replicate_rec_def = new_axiom 
  `!x ty y n. n > &0 ==> (array_at(x, ty, replicate(n, y)) -|- data_at(x, ty, y) ** array_at(x + (sizeof ty), ty, replicate(n - &1, y)))`
;;
add_to_database "array_at_replicate_rec_def" array_at_replicate_rec_def;;

let undef_array_at_zero_length = new_axiom
  `!x ty. undef_array_at(x, ty, &0) -|- emp`
;;
add_to_database "undef_array_at_zero_length" undef_array_at_zero_length

let undef_array_at_rec_def = new_axiom
  `!x ty n. n > &0 ==> (undef_array_at(x, ty, n) -|- undef_data_at(x, ty) ** undef_array_at(x + (sizeof ty), ty, n - &1))`
;;
add_to_database "undef_array_at_rec_def" undef_array_at_rec_def;;

let array_at_last_split = new_axiom
  `!x ty y n. n >= &0 ==> (array_at(x, ty, replicate(n, y)) ** data_at(x + n * (sizeof ty), ty, y) |-- array_at(x, ty, replicate(n + &1, y)))`
;;
add_to_database "array_at_last_split" array_at_last_split;;

(* forall *)
let skipn_def = define 
` skipn 0 l = l /\
  skipn (SUC n) NIL = NIL /\
  skipn (SUC n) (CONS (h:int) t) = skipn n t `
;;
add_to_database "skipn_def" skipn_def;;

let firstn_def = define
` firstn 0 l = NIL /\
  firstn (SUC n) NIL = NIL /\
  firstn (SUC n) (CONS (h:int) t) = CONS h (firstn n t) `
;;
add_to_database "firstn_def" firstn_def;;

let nth_def = define 
` nth 0 (CONS (h:int) t) = h /\
  nth (SUC n) (CONS h t) = nth n t `
;;
add_to_database "nth_def" nth_def;;

let ilength_map_id = 
  prove(`!(f:int->A) l. ilength (MAP f l) == ilength l`,
    GEN_TAC THEN LIST_INDUCT_TAC THENL
      [ REWRITE_TAC[MAP; ilength_def];
        ASM_REWRITE_TAC[MAP; ilength_def] ])
;;
add_to_database "ilength_map_id" ilength_map_id;;

let ilength_ge_0 = 
  prove(`!(l:int list). ilength l >= &0`,
    LIST_INDUCT_TAC THENL
    [ REWRITE_TAC[ilength_def] THEN ARITH_TAC;
      REWRITE_TAC[ilength_def] THEN ASM_ARITH_TAC ])
;;
add_to_database "ilength_ge_0" ilength_ge_0;;

let ilength_firstn_id = new_axiom `!n (l:int list). n == ilength l ==> firstn (num_of_int n) l == l`;;
add_to_database "ilength_sublist_id" ilength_firstn_id;;

let array_split_first = new_axiom `!x ty v vs.
  array_at (x, ty, CONS v vs) -|- data_at (x, ty, v) ** array_at (x + (sizeof ty), ty, vs)`;;
add_to_database "array_split_first" array_split_first;;

let skipn_nth_split = new_axiom `!k n (l:int list). (skipn k (firstn n l)) == CONS (nth k l) (skipn (k + 1) (firstn n l))`;;
add_to_database "skipn_nth_split" skipn_nth_split;;

let num_of_int_add_one = new_axiom `!n. num_of_int (n + &1) == (num_of_int n) + 1`;;
add_to_database "num_of_int_add_one" num_of_int_add_one;;

let array_at_empty = new_axiom `!x ty. array_at(x, ty, []) -|- emp`;;
add_to_database "array_at_empty" array_at_empty;;

let skipn_firstn_empty = new_axiom `!n (l:int list). skipn n (firstn n l) = []`;;
add_to_database "skipn_firstn_empty" skipn_firstn_empty;;

let array_split_last = new_axiom`!x ty v vs.
  array_at(x, ty, APPEND vs [v]) -|- array_at(x, ty, vs) ** data_at(x + (ilength vs) * (sizeof ty), ty, v)`
;;
add_to_database "array_split_last" array_split_last;;

let sublist_length = new_axiom `!lo hi (l:int list). 
  ilength (skipn (num_of_int lo) (firstn (num_of_int hi) l)) = hi - lo`
;;
add_to_database "sublist_length" sublist_length;;

let firstn_n = new_axiom `!(l:int list). firstn (num_of_int (ilength l)) l == l`;;
add_to_database "firstn_n" firstn_n;;

let firstn_nth_merge = new_axiom `!n (l:int list).
  APPEND (firstn (num_of_int n) l) [nth (num_of_int n) l] = firstn (num_of_int (n + &1)) l`
;;
add_to_database "firstn_nth_merge" firstn_nth_merge;;


