(** The abstract syntax tree of a Cstar program. *)

(** Identifier. *)
type ident = string [@@deriving show]

(** Source location information. *)
type loc = {line_no: int; col_no: int} [@@deriving show]

let pp_loc fmt loc = Format.fprintf fmt "%d:%d" loc.line_no loc.col_no

(** Source range information. *)
type range = {start_p: loc; end_p: loc} [@@deriving show]

let pp_range fmt r =
  Format.fprintf fmt "<%a-%a>" pp_loc r.start_p pp_loc r.end_p

type string_literal =
  { value: string  (** the string literal *)
  ; literal: string list  (** the raw string literal, parsed as is. *) }
[@@deriving show]

let concat_string_literal l1 l2 =
  {value= l1.value ^ l2.value; literal= l1.literal @ l2.literal}

(** Constants. *)
type constant =
  | Cinteger of int  (** Overloaded integer literals: [int], [Z]. *)
  | Cboolean of bool
      (** Overloaded boolean literals [true] and [false]: [_Bool], [bool], [prop], [hprop]. *)
  | Cstring of string_literal  (** string literals. *)
  | Cnullval  (** [val nullval]. *)
[@@deriving show]

(** Types. No anonymous struct/union. *)
and typ =
  | Tvoid  (** [void] *)
  | T_Bool  (** [_Bool], the C program bool type **)
  | Tint  (** [int], the C 32-bit integer *)
  | Tunsigned  (** [unsigned], the C 32-bit unsigned integer *)
  | Tprop  (** [PROP], the Cstar prop type *)
  | Thprop  (** [HPROP], seperation logic propsition *)
  | Tptr of typ  (** [<typ> *] *)
  | Tarray of typ * constexpr option  (** [<typ> [<len>]] *)
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
and unary_operator =
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
and binary_operator =
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
  | Osep  (** [SEP]. seperation logic conjunction *)
  | Osepand  (** [SEPAND]. seperation logic and *)
[@@deriving show]

(** function symbol prototype. *)
and funsym = typ * ident * parameter list * range [@@deriving show]

(** Initializers. *)
and init =
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
  | Ebackquoted of string  (** backquoted. *)
  | Evar of ident  (** variables. *)
  | Eunary of unary_operator * expr
  | Ebinary of binary_operator * expr * expr
  | Ecall of expr * expr list
  | Esizeofexpr of expr
  | Esizeoftyp of typ
  | Ecast of typ * expr
  | Econditional of expr * expr * expr
  | Elet_data_at of expr * typ * ident
[@@deriving show]

(** Const expressions. *)
and constexpr = {expr: expr; mutable value: constant option}
[@@deriving show]

and cstar_datatype =
  {name: ident; constructors: (ident * parameter list) list}
[@@deriving show]

(** Annotations. always wrapped in [/*@ @*/]*)
and attribute = Acstar of cstar_attribute [@@deriving show]

and cstar_attribute =
  | Afunction of declaration
  | Arepresentation of declaration
  | Apredicate of declaration
  | Adatatype of cstar_datatype
  | Aparameter of parameter list
  | Arequire of expr
  | Aensure of expr
  | Alocalvar of declaration
  | Ainvariant of expr
  | Aassert of expr
  | Acommand of stmt
  | Aargument of expr list
[@@deriving show]

(** Statements. *)
and stmt =
  | Sskip of attribute list * range
  | Sblock of stmt list * range
  | Sexpr of expr * attribute list * range
  | Sif of expr * stmt * stmt option * attribute list * range
  | Swhile of expr * stmt * attribute list * range
      (** optionally preceded by a invariant (written as [/*@ invariant <expr>*/])*)
  | Sbreak of range
  | Scontinue of range
  | Sreturn of expr option * range
  | Sdecl of declaration  (** local declarations. *)
[@@deriving show]

(** Declarations. *)
and declaration =
  | Ddeclvar of typ * ident * init option * range
      (** variable declaration. *)
  | Ddeclfun of funsym * attribute list  (** function declaration. *)
  | Ddecltype of typ * range  (** type definition. *)
  | Ddecltypedef of ident * typ * range  (** type definition. *)
  | Ddeffun of funsym * attribute list * stmt  (** function definition. *)
  | Dattribute of attribute * range  (** attribute declaration. *)
[@@deriving show]

(** Program. *)
and program = declaration list [@@deriving show]
