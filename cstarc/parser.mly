(*
Jacques-Henri Jourdan, Inria Paris
François Pottier, Inria Paris

Copyright (c) 2016-2017, Inria
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of Inria nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL INRIA BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* WARNING. When processing this grammar, Menhir should announce that
   ONE shift/reduce conflict was silently solved and that ONE state
   has 3 reduce/reduce conflicts on RPAREN, LPAREN, and LBRACK. If you
   modify the grammar, you should check that this is still the case. *)

(* Modified by Yiyuan Cao *)
(* Documentation for writting a (menhir) parser file: 
   https://ocaml.org/manual/5.2/lexyacc.html
   https://gallium.inria.fr/~fpottier/menhir/manual.html *)

%{
  open Ast
  open Context
  open Declarator

  let mk_loc { Lexing.pos_lnum; pos_cnum; pos_bol; _ } = { line_no = pos_lnum; col_no = pos_cnum - pos_bol }
  let mk_range (start_p, end_p) = { start_p = mk_loc start_p; end_p = mk_loc end_p }

  (* function composition *)
  let ( *.* ) f g x = f (g x)
  let id x = x

  (* [a -? b] is [x] if [a] is [Some x], and [b] otherwise. *)
  let ( -? ) a b = Option.value a ~default:b

  type data_type = Dint | Dchar | Dshort | Dlong | Dfloat | Ddouble
  type primitive_type = { data_type: data_type; signed: bool }
  let typ_of_primitive { data_type; signed } = 
    match data_type with
    | Dint -> if signed then Tint else Tunsigned
    | _ -> failwith "unsupported primitive type"

  type type_specifier = 
    | Sdata of data_type
    | Ssigness of bool
  let primitive_of_specifiers ss = 
    let open Core in
    let t = ref { data_type = Dint; signed = true } in
    List.iter ss ~f:(function
      | Sdata d -> t := { !t with data_type = d }
      | Ssigness s -> t := { !t with signed = s });
    !t

  let mk_constexpr e = 
    { expr= e; 
      value= match e with
        | Econst c -> Some c
        | _ -> None }
%}

%token<string> NAME
%token VARIABLE TYPE
%token<Ast.constant> CONSTANT 
%token<Ast.string_literal> STRING_LITERAL

%token ALIGNAS "_Alignas"
%token ALIGNOF "_Alignof"
%token ATOMIC "_Atomic"
%token AUTO "auto"
%token BOOL "_Bool"
%token BREAK "break"
%token CASE "case"
%token CHAR "char"
%token COMPLEX "_Complex"
%token CONST "const"
%token CONTINUE "continue"
%token DEFAULT "default"
%token DO "do"
%token DOUBLE "double"
%token ELSE "else"
%token ENUM "enum"
%token EXTERN "extern"
%token FLOAT "float"
%token FOR "for"
%token GENERIC "_Generic"
%token GOTO "goto"
%token IF "if"
%token IMAGINARY "_Imaginary"
%token INLINE "inline"
%token INT "int"
%token LONG "long"
%token NORETURN "_Noreturn"
%token REGISTER "register"
%token RESTRICT "restrict"
%token RETURN "return"
%token SHORT "short"
%token SIGNED "signed"
%token SIZEOF "sizeof"
%token STATIC "static"
%token STATIC_ASSERT "_Static_assert"
%token STRUCT "struct"
%token SWITCH "switch"
%token THREAD_LOCAL "_Thread_local"
%token TYPEDEF "typedef"
%token UNION "union"
%token UNSIGNED "unsigned"
%token VOID "void"
%token VOLATILE "volatile"
%token WHILE "while"

%token ELLIPSIS "..."
%token ADD_ASSIGN "+="
%token SUB_ASSIGN "-="
%token MUL_ASSIGN "*="
%token DIV_ASSIGN "/="
%token MOD_ASSIGN "%="
%token OR_ASSIGN "|="
%token AND_ASSIGN "&="
%token XOR_ASSIGN "^="
%token LEFT_ASSIGN "<<="
%token RIGHT_ASSIGN ">>="
%token LEFT "<<"
%token RIGHT ">>"
%token EQEQ "=="
%token NEQ "!="
%token LEQ "<="
%token GEQ ">="
%token EQ "="
%token LT "<"
%token GT ">"
%token INC "++"
%token DEC "--"
%token PTR "->"
%token PLUS "+"
%token MINUS "-"
%token STAR "*"
%token SLASH "/"
%token PERCENT "%"
%token BANG "!"
%token ANDAND "&&"
%token BARBAR "||"
%token AND "&"
%token BAR "|"
%token HAT "^"
%token QUESTION "?"
%token COLON ":"
%token TILDE "~"
%token LBRACE "{"
%token RBRACE "}"
%token LBRACK "["
%token RBRACK "]"
%token LPAREN "("
%token RPAREN ")"
%token SEMICOLON ";"
%token COMMA ","
%token DOT "."

%token COLONCOLON "::"
%token CSTAR_FUNCTION "cstar::function"
%token CSTAR_REPRESENTATION "cstar::representation"
%token CSTAR_PREDICATE "cstar::predicate"
%token CSTAR_DATATYPE "cstar::datatype"

%token SEP "SEP"
%token SEPAND "SEPAND"
%token PROP "PROP"
%token HPROP "HPROP"
%token LET_DATA_AT "LET_DATA_AT"

(* ATOMIC_LPAREN is "special"; it's used for left parentheses that
   follow the ["_Atomic"] keyword. It isn't given a token alias *)
%token ATOMIC_LPAREN

%token EOF

%type<context> save_context
%type<string> typedef_name var_name general_identifier enumeration_constant
%type<declarator> declarator direct_declarator

(* There is a reduce/reduce conflict in the grammar. It corresponds to the
   conflict in the second declaration in the following snippet:

     typedef int T;
     int f(int(T));

   It is specified by 6.7.6.3 11: 'T' should be taken as the type of the
   parameter of the anonymous function taken as a parameter by f (thus,
   f has type (T -> int) -> int).

   The reduce/reduce conflict is solved by letting menhir reduce the production
   appearing first in this file. This is the reason why we have the
   [typedef_name_spec] proxy: it is here just to make sure the conflicting
   production appears before the other (which concerns [general_identifier]). *)

(* These precedence declarations solve the dangling else conflict. *)
%nonassoc below_ELSE
%nonassoc ELSE

%start<Ast.program> translation_unit_file

%%

(* Helpers *)

(* [option(X)] represents a choice between nothing and [X].
   [ioption(X)] is the same thing, but is inlined at its use site,
   which in some cases is necessary in order to avoid a conflict.
   By convention, [X?] is syntactic sugar for [option(X)]. *)

// %inline ioption(X):
// | /* nothing */
//     { None }
// | x=X
//     { Some x }

// option(X):
// | o=ioption(X)
//     { o }

// (* By convention, [X*] is syntactic sugar for [list(X)]. *)

// list(X):
// | /* nothing */
//     { [] }
// | x=X xs=list(X)
//     { x::xs }

(* A list of A's and B's that contains exactly one A: *)

list_eq1(A, B):
| a=A bs=B*
    { (a, bs) }
| b=B xs=list_eq1(A, B)
    { let (a, bs) = xs in (a, b::bs) }

(* A list of A's and B's that contains at least one A: *)

list_ge1(A, B):
| a=A bs=B*
    { ([a], bs) }
| a=A xs=list_ge1(A, B)
    { let (a_s, bs) = xs in (a::a_s, bs) }
| b=B xs=list_ge1(A, B)
    { let (a_s, bs) = xs in (a_s, b::bs) }

(* A list of A's, B's and C's that contains exactly one A and exactly one B: *)

list_eq1_eq1(A, B, C):
| a=A xs=list_eq1(B, C)
    { let (b, cs) = xs in (a, b, cs) }
| b=B xs=list_eq1(A, C)
    { let (a, cs) = xs in (a, b, cs) }
| c=C xs=list_eq1_eq1(A, B, C)
    { let (a, b, cs) = xs in (a, b, c::cs) }

(* A list of A's, B's and C's that contains exactly one A and at least one B: *)

list_eq1_ge1(A, B, C):
| a=A xs=list_ge1(B, C)
    { let (bs, cs) = xs in (a, bs, cs) }
| b=B xs=list_eq1(A, C)
    { let (a, cs) = xs in (a, [b], cs) }
| b=B xs=list_eq1_ge1(A, B, C)
    { let (a, bs, cs) = xs in (a, b::bs, cs) }
| c=C xs=list_eq1_ge1(A, B, C)
    { let (a, bs, cs) = xs in (a, bs, c::cs) }

(* Upon finding an identifier, the lexer emits two tokens. The first token,
   [NAME], indicates that a name has been found; the second token, either [TYPE]
   or [VARIABLE], tells what kind of name this is. The classification is
   performed only when the second token is demanded by the parser. *)

typedef_name:
| i=NAME TYPE
    { i }

var_name:
| i=NAME VARIABLE
    { i }

(* [typedef_name_spec] must be declared before [general_identifier], so that the
   reduce/reduce conflict is solved the right way. *)

typedef_name_spec:
| i=typedef_name
    { i }

general_identifier:
| i=typedef_name
| i=var_name
    { i }

save_context:
| (* empty *)
    { save_context () }

scoped(X):
| ctx=save_context x=X
    { restore_context ctx; x }

(* [declarator_varname] and [declarator_typedefname] are like [declarator]. In
   addition, they have the side effect of introducing the declared identifier as
   a new variable or typedef name in the current context. *)

declarator_varname:
| d=declarator
    { declare_varname (identifier d); d }

declarator_typedefname:
| d=declarator
    { declare_typedefname (identifier d); d }

(* Merge source-level string literals. *)
string_literal:
| s=STRING_LITERAL
    { s }
| ss=string_literal s=STRING_LITERAL
    { concat_string_literal ss s }

(* End of the helpers, and beginning of the grammar proper: *)

primary_expression:
| n=var_name
    { Evar n }
| c=CONSTANT
    { Econst c }
| s=string_literal
    { Econst (Cstring s) }
| "(" e=expression ")"
    { e }
| generic_selection
    { failwith "unsupported generic selection" }

generic_selection:
| "_Generic" "(" assignment_expression "," generic_assoc_list ")"
    {}

generic_assoc_list:
| generic_association
| generic_assoc_list "," generic_association
    {}

generic_association:
| type_name ":" assignment_expression
| "default" ":" assignment_expression
    {}

postfix_expression:
| e=primary_expression
    { e }
| e1=postfix_expression "[" e2=expression "]"
    { Ebinary (Oindex, e1, e2) }
| e=postfix_expression "(" es=argument_expression_list? ")"
    { Ecall (e, es -? []) }
| e=postfix_expression "." i=general_identifier
    { Eunary (Odot i, e) }
| e=postfix_expression "->" i=general_identifier
    { Eunary (Oarrow i, e) }
| postfix_expression "++"
| postfix_expression "--"
    { failwith "unsupported postfix operator" }
| "(" t=type_name ")" "{" i=initializer_list ","? "}"
    { Ecomplit (t, i) }

argument_expression_list:
| e=assignment_expression
    { [e] }
| es=argument_expression_list "," e=assignment_expression
    { es @ [e] }

unary_expression:
| e=postfix_expression
    { e }
| "++" unary_expression
| "--" unary_expression
    { failwith "unsupported unary operator" }
| o=unary_operator e=cast_expression
    { Eunary (o, e) }
| "sizeof" e=unary_expression
    { Esizeofexpr e }
| "sizeof" "(" t=type_name ")"
    { Esizeoftyp t }
| "_Alignof" "(" type_name ")"
    { failwith "unsupported alignof" }
| "LET_DATA_AT" "(" e=assignment_expression "," t=declaration_specifiers d=declarator_varname ")"
    { Elet_data_at (e, declarator_type d t, identifier d) }

unary_operator:
| "&"
    { Oaddrof }
| "*"
    { Oderef }
| "+"
    { Oplus }
| "-"
    { Ominus }
| "~"
    { Obitneg }
| "!"
    { Olognot }

cast_expression:
| e=unary_expression
    { e }
| "(" t=type_name ")" e=cast_expression
    { Ecast (t, e) }

multiplicative_operator:
| "*"
    { Omul }
| "/" 
    { Odiv }
| "%" 
    { Omod }

multiplicative_expression:
| e=cast_expression
    { e }
| e1=multiplicative_expression o=multiplicative_operator e2=cast_expression
    { Ebinary (o, e1, e2) }

additive_operator:
| "+"
    { Oadd }
| "-"
    { Osub }

additive_expression:
| e=multiplicative_expression
    { e }
| e1=additive_expression o=additive_operator e2=multiplicative_expression
    { Ebinary (o, e1, e2) }

shift_operator:
| "<<" 
    { Obitlsh }
| ">>" 
    { Obitrsh }

shift_expression:
| e=additive_expression
    { e }
| e1=shift_expression o=shift_operator e2=additive_expression
    { Ebinary (o, e1, e2) }

relational_operator:
| "<"
    { Olt }
| ">" 
    { Ogt }
| "<=" 
    { Ole }
| ">=" 
    { Oge }

relational_expression:
| e=shift_expression
    { e }
| e1=relational_expression o=relational_operator e2=shift_expression
    { Ebinary (o, e1, e2) }

equality_operator:
| "==" 
    { Oeq }
| "!="
    { One }

equality_expression:
| e=relational_expression
    { e }
| e1=equality_expression o=equality_operator e2=relational_expression
    { Ebinary (o, e1, e2) }

and_expression:
| e=equality_expression
    { e }
| e1=and_expression "&" e2=equality_expression
    { Ebinary (Obitand, e1, e2) }

exclusive_or_expression:
| e=and_expression
    { e }
| e1=exclusive_or_expression "^" e2=and_expression
    { Ebinary (Obitxor, e1, e2) }

inclusive_or_expression:
| e=exclusive_or_expression
    { e }
| e1=inclusive_or_expression "|" e2=exclusive_or_expression
    { Ebinary (Obitor, e1, e2) }

logical_and_expression:
| e=inclusive_or_expression
    { e }
| e1=logical_and_expression "&&" e2=inclusive_or_expression
    { Ebinary (Ologand, e1, e2) }
| e1=logical_and_expression SEP e2=inclusive_or_expression
    { Ebinary (Osep, e1, e2) }
| e1=logical_and_expression SEPAND e2=inclusive_or_expression
    { Ebinary (Osepand, e1, e2) }

logical_or_expression:
| e=logical_and_expression
    { e }
| e1=logical_or_expression "||" e2=logical_and_expression
    { Ebinary (Ologor, e1, e2) }

conditional_expression:
| e=logical_or_expression
    { e }
| e1=logical_or_expression "?" e2=expression ":" e3=conditional_expression
    { Econditional (e1, e2, e3) }

assignment_expression:
| e=conditional_expression
    { e }
| e1=unary_expression o=assignment_operator e2=assignment_expression
    { Ebinary (o, e1, e2) }

assignment_operator:
| "="
    { Oassign }
| "*="
| "/="
| "%="
| "+="
| "-="
| "<<="
| ">>="
| "&="
| "^="
| "|="
    { failwith "unsupported assignment operator" }

expression:
| e=assignment_expression
    { e }
| e1=expression "," e2=assignment_expression
    { Ebinary (Ocomma, e1, e2) }


constant_expression:
| conditional_expression
    {}

(* We separate type declarations, which contain an occurrence of ["typedef"], and
   normal declarations, which do not. This makes it possible to distinguish /in
   the grammar/ whether a declaration introduces typedef names or variables in
   the context. *)

declaration:
| t=declaration_specifiers         ds=init_declarator_list(declarator_varname)?     ";"
    { match ds with
      | None -> [Ddecltype (t, mk_range $sloc)]
      | Some ds -> Core.List.map ds ~f:(fun (d, i) -> 
          if is_function_declarator d then
            Ddeclfun ((declarator_type d t, identifier d, parameters d, mk_range $sloc), [])
          else 
            Ddeclvar (declarator_type d t, identifier d, i, mk_range $sloc) ) }
| t=declaration_specifiers_typedef ds=init_declarator_list(declarator_typedefname)? ";"
    { match ds with
      | None -> [Ddecltype (t, mk_range $sloc)]
      | Some ds -> Core.List.map ds ~f:(fun (d, _) -> 
          Ddecltypedef (identifier d, declarator_type d t, mk_range $sloc) ) }
| static_assert_declaration
    { failwith "unsupported static assert" }

(* [declaration_specifier] corresponds to one declaration specifier in the C18
   standard, deprived of "typedef" and of type specifiers. *)

declaration_specifier:
| storage_class_specifier (* deprived of "typedef" *)
| type_qualifier
| function_specifier
| alignment_specifier
    {}

(* [declaration_specifiers] requires that at least one type specifier be
   present, and, if a unique type specifier is present, then no other type
   specifier be present. In other words, one should have either at least one
   nonunique type specifier, or exactly one unique type specifier.

   This is a weaker condition than 6.7.2 2. Encoding this condition in the
   grammar is necessary to disambiguate the example in 6.7.7 6:

     typedef signed int t;
     struct tag {
     unsigned t:4;
     const t:5;
     };

   The first field is a named t, while the second is unnamed of type t.

   [declaration_specifiers] forbids the ["typedef"] keyword. *)

declaration_specifiers:
| xs=list_eq1(type_specifier_unique,    declaration_specifier)
    { let (t, _) = xs in t }
| xs=list_ge1(type_specifier_nonunique, declaration_specifier)
    { let (ss, _) = xs in typ_of_primitive (primitive_of_specifiers ss) }

(* [declaration_specifiers_typedef] is analogous to [declaration_specifiers],
   but requires the ["typedef"] keyword to be present (exactly once). *)

declaration_specifiers_typedef:
| xs=list_eq1_eq1("typedef", type_specifier_unique,    declaration_specifier)
    { let (_, t, _) = xs in t }
| xs=list_eq1_ge1("typedef", type_specifier_nonunique, declaration_specifier)
    { let (_, ss, _) = xs in typ_of_primitive (primitive_of_specifiers ss) }

(* The parameter [declarator] in [init_declarator_list] and [init_declarator]
   is instantiated with [declarator_varname] or [declarator_typedefname]. *)

init_declarator_list(declarator):
| d=init_declarator(declarator)
    { [d] }
| ds=init_declarator_list(declarator) "," d=init_declarator(declarator)
    { ds @ [d] }

init_declarator(declarator):
| d=declarator
    { (d, None) }
| d=declarator "=" i=c_initializer
    { (d, Some i) }

(* [storage_class_specifier] corresponds to storage-class-specifier in the
   C18 standard, deprived of ["typedef"] (which receives special treatment). *)

storage_class_specifier:
| "extern"
| "static"
| "_Thread_local"
| "auto"
| "register"
    {}

(* A type specifier which can appear together with other type specifiers. *)

type_specifier_nonunique:
| "char"
    { Sdata Dchar }
| "short"
    { Sdata Dshort }
| "int"
    { Sdata Dint }
| "long"
    { Sdata Dlong }
| "float"
    { Sdata Dfloat }
| "double"
    { Sdata Ddouble }
| "signed"
    { Ssigness true}
| "unsigned"
    { Ssigness false }
| "_Complex"
    { failwith "unsupported complex" }

(* A type specifier which cannot appear together with other type specifiers. *)

type_specifier_unique:
| "void"
    { Tvoid }
| "_Bool"
    { T_Bool }
| "PROP"
    { Tprop }
| "HPROP"
    { Thprop }
| atomic_type_specifier
    { failwith "unsupported atomic" }
| t=struct_or_union_specifier
    { t }
| enum_specifier
    { failwith "unsupported enum" }
| i=typedef_name_spec
    { Tnamed i }

struct_or_union_specifier:
| su=struct_or_union i=general_identifier? "{" fs=struct_declaration_list "}"
    { match su with
      | `Struct -> Tstructdecl (i, fs)
      | `Union -> Tuniondecl (i, fs) }
| su=struct_or_union i=general_identifier
    { match su with
      | `Struct -> Tstruct i
      | `Union -> Tunion i }

struct_or_union:
| "struct"
    { `Struct }
| "union"
    { `Union }

struct_declaration_list:
| f=struct_declaration
    { f }
| fs=struct_declaration_list f=struct_declaration
    { fs @ f }

struct_declaration:
| t=specifier_qualifier_list ds=struct_declarator_list? ";"
    { match ds with
      | None -> []
      | Some ds -> Core.List.map ds ~f:(fun d -> (declarator_type d t, identifier d)) }
| static_assert_declaration
    { failwith "unsupported static assert" }


(* [specifier_qualifier_list] is as in the standard, except it also encodes the
   same constraint as [declaration_specifiers] (see above). *)

specifier_qualifier_list:
| xs=list_eq1(type_specifier_unique,    type_qualifier | alignment_specifier {})
    { let (t, _) = xs in t }
| xs=list_ge1(type_specifier_nonunique, type_qualifier | alignment_specifier {})
    { let (ss, _) = xs in typ_of_primitive (primitive_of_specifiers ss) }

struct_declarator_list:
| d=struct_declarator
    { [d] }
| ds=struct_declarator_list "," d=struct_declarator
    { ds @ [d] }

struct_declarator:
| d=declarator
    { d }
| declarator? ":" constant_expression
    { failwith "unsupported bitfield" }

enum_specifier:
| "enum" general_identifier? "{" enumerator_list ","? "}"
| "enum" general_identifier
    {}

enumerator_list:
| enumerator
| enumerator_list "," enumerator
    {}

enumerator:
| i=enumeration_constant
| i=enumeration_constant "=" constant_expression
    { declare_varname i }

enumeration_constant:
| i=general_identifier
    { i }

atomic_type_specifier:
| "_Atomic" "(" type_name ")"
| "_Atomic" ATOMIC_LPAREN type_name ")"
    { failwith "unsupported atomic" }

type_qualifier:
| "const"
| "restrict"
| "volatile"
| "_Atomic"
    {}

function_specifier:
  "inline" | "_Noreturn"
    {}

alignment_specifier:
| "_Alignas" "(" type_name ")"
| "_Alignas" "(" constant_expression ")"
    {}

declarator:
| p=ioption(pointer) d=direct_declarator
    { other_declarator d (p -? id) }

(* The occurrences of [save_context] inside [direct_declarator] and
   [direct_abstract_declarator] seem to serve no purpose. In fact, they are
   required in order to avoid certain conflicts. In other words, we must save
   the context at this point because the LR automaton is exploring multiple
   avenues in parallel and some of them do require saving the context. *)

direct_declarator:
| i=general_identifier
    { identifier_declarator i }
| "(" save_context d=declarator ")"
    { d }
| d=direct_declarator "[" type_qualifier_list? e=assignment_expression? "]"
    { other_declarator d (match e with
      | Some e -> fun t -> Tarray (t, Some (mk_constexpr e))
      | None -> fun t -> Tarray (t, None) ) }
| d=direct_declarator "[" "static" type_qualifier_list? e=assignment_expression "]"
| d=direct_declarator "[" type_qualifier_list "static" e=assignment_expression "]"
    { other_declarator d (fun t -> Tarray (t, Some (mk_constexpr e))) }
| d=direct_declarator "[" type_qualifier_list? "*" "]"
    { other_declarator d (fun t -> Tarray (t, None)) }
| d=direct_declarator "(" ps=scoped(parameter_type_list) ")"
    { let (ctx, ps) = ps in function_declarator d ctx ps }
| d=direct_declarator "(" save_context is=identifier_list? ")"
    { match is with
      | None -> other_declarator d id
      | Some _ -> failwith "unsupported function declarator" }

pointer:
| "*" type_qualifier_list? p=pointer?
    { match p with
      | None -> fun t -> Tptr t
      | Some p -> fun t -> p (Tptr t) }

type_qualifier_list:
| type_qualifier_list? type_qualifier
    {}

parameter_type_list:
| ps=parameter_list option("," "..." {}) ctx=save_context
    { (ctx, ps) }

parameter_list:
| p=parameter_declaration
    { [p] }
| ps=parameter_list "," p=parameter_declaration
    { ps @ [p] }

parameter_declaration:
| t=declaration_specifiers d=declarator_varname
    { (declarator_type d t, identifier d) }
| declaration_specifiers abstract_declarator?
    { failwith "unsupported abstract declarator" }

identifier_list:
| var_name
| identifier_list "," var_name
    {}

(* We treat declarator as `typ -> typ`, for example, when parsing a type `int*[]`,
    we first parse `int` as a type, then parse `*[]` as a declarator, and finally
    apply the declarator to the type. *)

type_name:
| t=specifier_qualifier_list d=abstract_declarator?
    { (d -? id) t }

abstract_declarator:
| p=pointer
    { p }
| p=ioption(pointer) d=direct_abstract_declarator
    { d *.* (p -? id) }

direct_abstract_declarator:
| "(" save_context abstract_declarator ")"
    { failwith "unsupported abstract declarator" }
| d=direct_abstract_declarator? "[" ioption(type_qualifier_list) e=assignment_expression? "]"
    { (d -? id) *.* match e with
      | Some e -> fun t -> Tarray (t, Some (mk_constexpr e))
      | None -> fun t -> Tarray (t, None) }
| d=direct_abstract_declarator? "[" "static" type_qualifier_list? e=assignment_expression "]"
| d=direct_abstract_declarator? "[" type_qualifier_list "static" e=assignment_expression "]"
    { (d -? id) *.* (fun t -> Tarray (t, Some (mk_constexpr e))) }
| d=direct_abstract_declarator? "[" "*" "]"
    { (d -? id) *.* fun t -> Tarray (t, None) }
| ioption(direct_abstract_declarator) "(" scoped(parameter_type_list)? ")"
    { failwith "unsupported abstract declarator" }

c_initializer:
| e=assignment_expression
    { Init_single e }
| "{" i=initializer_list ","? "}"
    { i }

initializer_list:
| d=designation? i=c_initializer
    { match d with
      | None -> Init_array [i]
      | Some d -> Init_struct [(d, i)] }
| is=initializer_list "," d=designation? i=c_initializer
    { match (is, d) with
      | (Init_array is, None) -> Init_array (is @ [i])
      | (Init_struct is, Some d) -> Init_struct (is @ [(d, i)])
      | _ -> failwith "unsupported initializer list" }

designation:
| d=designator_list "="
    { d }

designator_list:
| ds=designator_list? d=designator
    { match ds with
      | None -> d
      | Some _ -> failwith "unsupported designator list" }

designator:
| "[" constant_expression "]"
    { failwith "unsupported designator" }
| "." i=general_identifier
    { i }

static_assert_declaration:
| "_Static_assert" "(" constant_expression "," string_literal ")" ";"
    {}

statement:
| s=labeled_statement
| s=scoped(compound_statement)
| s=expression_statement
| s=scoped(selection_statement)
| s=scoped(iteration_statement)
| s=jump_statement
    { s }

labeled_statement:
| general_identifier ":" s=statement
| "case" constant_expression ":" s=statement
| "default" ":" s=statement
    { s }

compound_statement:
| "{" ss=block_item_list? "}"
    { Sblock (ss -? [], mk_range $sloc) }

block_item_list:
| ss=block_item_list? s=block_item
    { (ss -? []) @ s }

block_item:
| d=declaration
    { Core.List.map d ~f:(fun d -> Sdecl d) }
| s=statement
    { [s] }

expression_statement:
| e=expression? ";"
    { match e with
      | None -> Sskip (mk_range $sloc)
      | Some e -> Sdo (e, mk_range $sloc) }

selection_statement:
| "if" "(" e=expression ")" st=scoped(statement) "else" se=scoped(statement)
    { Sif (e, st, Some se, mk_range $sloc) }
| "if" "(" e=expression ")" st=scoped(statement) %prec below_ELSE
    { Sif (e, st, None, mk_range $sloc) }
| "switch" "(" expression ")" scoped(statement)
    { failwith "unsupported switch" }

iteration_statement:
| "while" "(" e=expression ")" s=scoped(statement)
    { Swhile (e, None, s, mk_range $sloc) }
| "do" scoped(statement) "while" "(" expression ")" ";"
    { failwith "unsupported do-while" }
| "for" "(" expression? ";" expression? ";" expression? ")" scoped(statement)
| "for" "(" declaration expression? ";" expression? ")" scoped(statement)
    { failwith "unsupported for" }

jump_statement:
| "goto" general_identifier ";"
    { failwith "unsupported goto" }
| "continue" ";"
    { Scontinue (mk_range $sloc) }
| "break" ";"
    { Sbreak (mk_range $sloc) }
| "return" e=expression? ";"
    { Sreturn (e, mk_range $sloc) }

translation_unit_file:
| d=external_declaration ds=translation_unit_file 
    { d @ ds }
| d=external_declaration EOF
    { d }

external_declaration:
| d=function_definition
    { [d] }
| d=declaration
    { d }
| a=attribute_specifier ";"
    { Core.List.map a ~f:(fun a -> Dattribute (a, mk_range $sloc)) }

function_definition1:
| t=declaration_specifiers d=declarator_varname
    { let ctx = save_context () in
      reinstall_function_context d;
      (ctx, (declarator_type d t, identifier d, parameters d, mk_range $sloc)) }

function_definition:
| ctx=function_definition1 d=declaration_list? s=compound_statement
    { let (ctx, f) = ctx in
      restore_context ctx; match d with 
      | None -> Ddeffun (f, [], s) 
      | Some _ -> failwith "unsupported K&R function definition" }

declaration_list:
| declaration
| declaration_list declaration
    {}

(**************************************************)
(*                  Annotations                   *)
(**************************************************)

attribute_specifier:
| "[" "[" a=attribute_list "]" "]" 
    { a }

attribute_list:
| x=attribute
    { x }
| xs=attribute_list "," x=attribute
    { xs @ x }

attribute:
| x=cstar_attribute
    { [x] }
| attribute_token attribute_argument_clause?
    { [] }

attribute_token:
| standard_attribute
| attribute_prefixed_token
    {}

standard_attribute:
| general_identifier
    {}

attribute_prefixed_token:
| attribute_prefix "::" general_identifier
    {}

attribute_prefix:
| general_identifier
    {}

attribute_argument_clause:
| "(" balanced_token_sequence? ")"
    {}

balanced_token_sequence:
| balanced_token+
    {}

balanced_token:
| "(" balanced_token_sequence? ")"
| "[" balanced_token_sequence? "]"
| "{" balanced_token_sequence? "}"
| NAME
| TYPE
| CONSTANT 
| STRING_LITERAL
| "_Alignas"
| "_Alignof"
| "_Atomic"
| "auto"
| "_Bool"
| "break"
| "case"
| "char"
| "_Complex"
| "const"
| "continue"
| "default"
| "do"
| "double"
| "else"
| "enum"
| "extern"
| "float"
| "for"
| "_Generic"
| "goto"
| "if"
| "_Imaginary"
| "inline"
| "int"
| "long"
| "_Noreturn"
| "register"
| "restrict"
| "return"
| "short"
| "signed"
| "sizeof"
| "static"
| "_Static_assert"
| "struct"
| "switch"
| "_Thread_local"
| "typedef"
| "union"
| "unsigned"
| "void"
| "volatile"
| "while"
| "::"
| "..."
| "+="
| "-="
| "*="
| "/="
| "%="
| "|="
| "&="
| "^="
| "<<="
| ">>="
| "<<"
| ">>"
| "=="
| "!="
| "<="
| ">="
| "="
| "<"
| ">"
| "++"
| "--"
| "->"
| "+"
| "-"
| "*"
| "/"
| "%"
| "!"
| "&&"
| "||"
| "&"
| "|"
| "^"
| "?"
| ":"
| "~"
| ";"
| ","
| "."
    {}

cstar_attribute:
| x=cstar_function_attribute
| x=cstar_representation_attribute
| x=cstar_predicate_attribute
| x=cstar_datatype_attribute
    { x }

cstar_function_attribute:
| CSTAR_FUNCTION "(" d=function_definition ")"
    { Acstar (Afunction d) }

cstar_representation_attribute:
| CSTAR_REPRESENTATION "(" d=function_definition ")"
    { Acstar (Arepresentation d) }

cstar_predicate_attribute:
| CSTAR_PREDICATE "(" d=function_definition ")"
    { Acstar (Apredicate d) }

cstar_datatype_attribute:
| CSTAR_DATATYPE "(" d=cstar_datatype_definition ")"
    { Acstar (Adatatype d) }

cstar_datatype_definition:
| i=cstar_datatype_name "," cs=cstar_datatype_constructor_list ","?
    { {name= i; constructors= cs} }

cstar_datatype_name:
| i=general_identifier 
    { declare_typedefname i; i }

cstar_datatype_constructor_list:
| c=cstar_datatype_constructor
    { [c] }
| cs=cstar_datatype_constructor_list "," c=cstar_datatype_constructor
    { cs @ [c] }

cstar_datatype_constructor:
| d=declarator_varname
    { (identifier d, parameters d) }
