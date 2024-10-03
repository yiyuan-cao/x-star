(** The abstract syntax tree of a Cstar program. *)

(** Identifier. *)
type ident = string [@@deriving show]

(** Source location information. *)
type loc = {line_no: int; col_no: int} [@@deriving show]

(** Source range information. *)
type range = {start_p: loc; end_p: loc} [@@deriving show]

(** Constants. *)
type constant =
  | Cinteger of int  (** Overloaded integer literals: [int], [Z]. *)
  | Cboolean of bool
      (** Overloaded boolean literals [true] and [false]: [_Bool], [bool], [prop], [hprop]. *)
  | Cnullval  (** [val nullval]. *)
[@@deriving show]

(** Types. No anonymous struct/union. *)
type typ =
  | Tvoid  (** [void] *)
  | T_Bool  (** [_Bool], the C program bool type **)
  | Tint  (** [int], the C 32-bit integer *)
  | Tunsigned  (** [unsigned], the C 32-bit unsigned integer *)
  | Tptr of typ  (** [<typ> *] *)
  | Tarray of typ * int option  (** [<typ> [<len>]] *)
  | Tstruct of ident  (** struct <ident> *)
  | Tstructdecl of ident option * field list
      (** struct <ident> { <field> ... } *)
  | Tunion of ident  (** union <ident> *)
  | Tuniondecl of ident option * field list
      (** union <ident> { <field> ... } *)
  | Tnamed of ident  (** [<ident>], type indentifiers of [indtype]s *)
[@@deriving show]

(** Typed parameter. *)
and parameter = typ * ident [@@deriving show]

(** Composite (struct or union) field. *)
and field = parameter [@@deriving show]

(** Unary operators. *)
type unary_operator =
  | Ominus  (** unary [-] *)
  | Oplus  (** unary [+] *)
  | Olognot  (** [!] *)
  | Obitneg  (** [~] bitwise complement *)
  | Oderef  (** unary [*] *)
  | Oaddrof  (** [&] *)
  | Odot of ident  (** [. <ident>] member access *)
  | Oarrow of ident  (** [-> <ident>] pointer member access *)
[@@deriving show]

(** Binary operators. *)
type binary_operator =
  | Omul  (** binary [*] *)
  | Odiv  (** [/] *)
  | Omod  (** [%] *)
  | Oadd  (** binary [+] *)
  | Osub  (** binary [-] *)
  | Olt  (** [<]. return type overloaded: [_Bool], [bool], [prop]. *)
  | Ogt  (** [>]. return type overloaded: [_Bool], [bool], [prop]. *)
  | Ole  (** [<=]. return type overloaded: [_Bool], [bool], [prop]. *)
  | Oge  (** [>=]. return type overloaded: [_Bool], [bool], [prop]. *)
  | Oeq  (** [==]. return type overloaded: [_Bool], [bool], [prop]. *)
  | One  (** [!=]. return type overloaded: [_Bool], [bool], [prop]. *)
  | Oindex  (** [<expr>[<expr>]], array indexing *)
  | Ologand
      (** [&&]. Overloaded: [_Bool], [bool], [prop], [hprop]. Short-circuit behavior for [_Bool]. *)
  | Ologor
      (** [||]. Overloaded: [_Bool], [bool], [prop], [hprop]. Short-circuit behavior for [_Bool]. *)
  | Obitand  (** [&] bitwise AND *)
  | Obitor  (** [|] bitwise OR *)
  | Obitxor  (** [^] bitwise XOR *)
  | Obitrsh  (** [>>] right shift *)
  | Obitlsh  (** [<<] left shift *)
  | Oassign  (** [=] *)
  | Ocomma
      (** [,] sequence effecful expressions, return the result of the latter *)
[@@deriving show]

(** function symbol prototype. *)
type funsym = typ * ident * parameter list * range [@@deriving show]

(** Initializers. *)
type init =
  | Init_single of expr
  | Init_struct of (ident * init) list
      (** [{.<ident> = init, ...}] for union and struct composite literal *)
  | Init_array of init list
[@@deriving show]

(** Expressions. *)
and expr =
  | Econst of constant  (** literal values. *)
  | Ecomplit of typ * init
      (** [(_struct ident) { init_list }]. Composite initializer. *)
  | Ebackquoted of expr  (** backquoted. *)
  | Evar of ident  (** variables. *)
  | Eunary of unary_operator * expr
  | Ebinary of binary_operator * expr * expr
  | Ecall of expr * expr list
  | Esizeofexpr of expr
  | Esizeoftyp of typ
  | Ecast of typ * expr
  | Econditional of expr * expr * expr
[@@deriving show]

(** Struct or union. *)
type struct_or_union = Struct | Union [@@deriving show]

(** Elements of proofs. Currently a string literal for Coq tactics.  *)
type tactic = string [@@deriving show]

(** Annotations. always wrapped in [/*@ @*/]*)
type annotation =
  | Arequire of expr * range
      (** formula (of type [prop]) is indistinguishable from [expr] syntactically. *)
  | Aensure of expr * range
  | Aassertion of expr * range
      (** internal assertions. including loop invariants. *)
  | Aparameter of parameter list * range  (** Logical variables. *)
  | Aproof of ident * tactic * range
      (** proof script in programs, with identifier label. *)
  | Aimplies of expr * expr * ident * range
      (** [/*@ implies(<expr>, <expr>, <ident>) @*/]. *)
[@@deriving show]

(** Function annotation list. *)
type annotations = annotation list [@@deriving show]

(** Constructors of inductive data types. *)
type constructor = funsym [@@deriving show]

(** A inductive data type definition. *)
type indtype = ident * constructor list * range [@@deriving show]

(** Statements. *)
type stmt =
  | Sskip of range
  | Sblock of stmt list * range
  | Sdo of expr * range
  | Sif of expr * stmt * stmt option * range
  | Swhile of expr * annotation option * stmt * range
      (** optionally preceded by a invariant (written as [/*@ invariant <expr>*/])*)
  | Sbreak of range
  | Scontinue of range
  | Sreturn of expr option * range
  | Sdecl of declaration  (** local declarations. *)
  | Sannotation of annotation
      (** annotations. only [Aassertion]s make sense currently. *)
[@@deriving show]

(** Declarations. *)
and declaration =
  | Ddeclvar of typ * ident * init option * range
      (** variable declaration. *)
  | Ddeclcomp of typ * range  (** composite type declaration. *)
  | Ddeclfun of funsym * annotations  (** function declaration. *)
  | Ddecltype of typ * range  (** type definition. *)
  | Ddecltypedef of ident * typ * range  (** type definition. *)
  | Ddeffun of funsym * annotations * stmt  (** function definition. *)
[@@deriving show]

(** Program. *)
type program = declaration list [@@deriving show]

(** Builtin types and functions. TODO: use this. *)
type builtins =
  { builtin_typedefs: (ident * typ) list
  ; builtin_functions: (ident * typ * typ list) list }
