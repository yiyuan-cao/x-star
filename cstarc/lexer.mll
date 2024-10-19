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

(* Modified by Yiyuan Cao *)
(* Documentation for writting a mllex file: https://ocaml.org/manual/5.2/lexyacc.html *)

{
open Core
open Lexing
open Context
open Parser
open Options

let init _filename channel : Lexing.lexbuf =
  Lexing.from_channel channel

type string_literal_buf = 
  { value: Buffer.t
  ; literal: Buffer.t }
let new_string_literal_buf () = 
  { value= Buffer.create 17
  ; literal= Buffer.create 17 }

}

(* Identifiers *)
let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let nondigit = ['_' 'a'-'z' 'A'-'Z']

let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad

let identifier_nondigit =
    nondigit
  | universal_character_name

let identifier = identifier_nondigit (identifier_nondigit|digit)*

(* Whitespaces. '\r' is not considered as white-space by the standard,
   but we include it in order to accept files encoded with DOS-style
   line endings.  Beware : \011 and \012 are DECIMAL escape
   codes. They correspond to vertical tab and form feed,
   respectively. *)
let whitespace_char_no_newline = [' ' '\t' '\011' '\012' '\r']

(* Integer constants *)
let nonzero_digit = ['1'-'9']
let decimal_constant = nonzero_digit digit*

let octal_digit = ['0'-'7']
let octal_constant = '0' octal_digit*

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_constant =
  hexadecimal_prefix hexadecimal_digit+

let unsigned_suffix = ['u' 'U']
let long_suffix = ['l' 'L']
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?

let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?

(* Floating constants *)
let sign = ['-' '+']
let digit_sequence = digit+
let floating_suffix = ['f' 'l' 'F' 'L']

let fractional_constant =
    digit_sequence? '.' digit_sequence
  | digit_sequence '.'
let exponent_part =
    ['e' 'E'] sign? digit_sequence
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | digit_sequence exponent_part floating_suffix?

let hexadecimal_digit_sequence = hexadecimal_digit+
let hexadecimal_fractional_constant =
    hexadecimal_digit_sequence? '.' hexadecimal_digit_sequence
  | hexadecimal_digit_sequence '.'
let binary_exponent_part =
    ['p' 'P'] sign? digit_sequence
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix hexadecimal_digit_sequence
        binary_exponent_part floating_suffix?

(* Preprocessing numbers *)
let preprocessing_number =
  '.'? ['0'-'9']
  (['0'-'9' 'A'-'Z' 'a'-'z' '_' '.'] | ['e' 'E' 'p' 'P']['+' '-'])*

(* Character and string constants *)
let simple_escape_sequence =
  '\\' ['\''  '\"'  '?'  '\\'  'a'  'b'  'f'  'n'  'r'  't'  'v']
let octal_escape_sequence =
  '\\' (octal_digit
         | octal_digit octal_digit
         | octal_digit octal_digit octal_digit)
let hexadecimal_escape_sequence = "\\x" hexadecimal_digit+
let escape_sequence =
    simple_escape_sequence
  | octal_escape_sequence
  | hexadecimal_escape_sequence
  | universal_character_name

rule initial = parse
  | whitespace_char_no_newline+   { initial lexbuf }
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | "/*"                          { multiline_comment lexbuf; initial lexbuf }
  | "//"                          { singleline_comment lexbuf; initial_linebegin lexbuf }
  | integer_constant as c         { CONSTANT (Ast.Cinteger (int_of_string c)) }
  | decimal_floating_constant     { failwith "unsupported" }
  | hexadecimal_floating_constant { failwith "unsupported" }
  | preprocessing_number          { failwith "These characters form a preprocessor number, but not a constant" }
  | (['L' 'u' 'U']|"") "'"        { ignore (char lexbuf); char_literal_end lexbuf; failwith "unsupported" }
  | (['L' 'u' 'U']|""|"u8") "\""  { STRING_LITERAL (string_literal (new_string_literal_buf ()) lexbuf) }
  | "`"                           { RAW_STRING_LITERAL (raw_string_literal (Buffer.create 17) lexbuf) }

  | "[["                          { LBRACK_BRACK }
  | "]]"                          { RBRACK_BRACK }
  | "::"                          { COLONCOLON }
  | "cstar::function"             { CSTAR_FUNCTION }
  | "cstar::representation"       { CSTAR_REPRESENTATION }
  | "cstar::predicate"            { CSTAR_PREDICATE }
  | "cstar::datatype"             { CSTAR_DATATYPE }
  | "cstar::parameter"            { CSTAR_PARAMETER }
  | "cstar::require"              { CSTAR_REQUIRE }
  | "cstar::ensure"               { CSTAR_ENSURE }
  | "cstar::invariant"            { CSTAR_INVARIANT }
  | "cstar::ghostvar"             { CSTAR_GHOSTVAR }
  | "cstar::assert"               { CSTAR_ASSERT }
  | "cstar::ghostcommand"         { CSTAR_GHOSTCOMMAND }
  | "cstar::argument"             { CSTAR_ARGUMENT }
  | "SEP"                         { SEP }
  | "SEPAND"                      { SEPAND }
  | "PROP"                        { PROP }
  | "HPROP"                       { HPROP }
  | "LET_DATA_AT"                 { LET_DATA_AT }

  | "..."                         { ELLIPSIS }
  | "+="                          { ADD_ASSIGN }
  | "-="                          { SUB_ASSIGN }
  | "*="                          { MUL_ASSIGN }
  | "/="                          { DIV_ASSIGN }
  | "%="                          { MOD_ASSIGN }
  | "|="                          { OR_ASSIGN }
  | "&="                          { AND_ASSIGN }
  | "^="                          { XOR_ASSIGN }
  | "<<="                         { LEFT_ASSIGN }
  | ">>="                         { RIGHT_ASSIGN }
  | "<<"                          { LEFT }
  | ">>"                          { RIGHT }
  | "=="                          { EQEQ }
  | "!="                          { NEQ }
  | "<="                          { LEQ }
  | ">="                          { GEQ }
  | "="                           { EQ }
  | "<"                           { LT }
  | ">"                           { GT }
  | "++"                          { INC }
  | "--"                          { DEC }
  | "->"                          { PTR }
  | "+"                           { PLUS }
  | "-"                           { MINUS }
  | "*"                           { STAR }
  | "/"                           { SLASH }
  | "%"                           { PERCENT }
  | "!"                           { BANG }
  | "&&"                          { ANDAND }
  | "||"                          { BARBAR }
  | "&"                           { AND }
  | "|"                           { BAR }
  | "^"                           { HAT }
  | "?"                           { QUESTION }
  | ":"                           { COLON }
  | "~"                           { TILDE }
  | "{"|"<%"                      { LBRACE }
  | "}"|"%>"                      { RBRACE }
  | "["|"<:"                      { LBRACK }
  | "]"|":>"                      { RBRACK }
  | "("                           { LPAREN }
  | ")"                           { RPAREN }
  | ";"                           { SEMICOLON }
  | ","                           { COMMA }
  | "."                           { DOT }
  | "_Alignas"                    { ALIGNAS }
  | "_Alignof"                    { ALIGNOF }
  | "_Atomic"                     { ATOMIC }
  | "_Bool"                       { BOOL }
  | "_Complex"                    { COMPLEX }
  | "_Generic"                    { GENERIC }
  | "_Imaginary"                  { IMAGINARY }
  | "_Noreturn"                   { NORETURN }
  | "_Static_assert"              { STATIC_ASSERT }
  | "_Thread_local"               { THREAD_LOCAL }
  | "auto"                        { AUTO }
  | "bool"                        { BOOL }
  | "break"                       { BREAK }
  | "case"                        { CASE }
  | "char"                        { CHAR }
  | "const"                       { CONST }
  | "continue"                    { CONTINUE }
  | "default"                     { DEFAULT }
  | "do"                          { DO }
  | "double"                      { DOUBLE }
  | "else"                        { ELSE }
  | "enum"                        { ENUM }
  | "extern"                      { EXTERN }
  | "float"                       { FLOAT }
  | "for"                         { FOR }
  | "goto"                        { GOTO }
  | "if"                          { IF }
  | "inline"                      { INLINE }
  | "int"                         { INT }
  | "long"                        { LONG }
  | "register"                    { REGISTER }
  | "restrict"                    { RESTRICT }
  | "return"                      { RETURN }
  | "short"                       { SHORT }
  | "signed"                      { SIGNED }
  | "sizeof"                      { SIZEOF }
  | "static"                      { STATIC }
  | "struct"                      { STRUCT }
  | "switch"                      { SWITCH }
  | "typedef"                     { TYPEDEF }
  | "union"                       { UNION }
  | "unsigned"                    { UNSIGNED }
  | "void"                        { VOID }
  | "volatile"                    { VOLATILE }
  | "while"                       { WHILE }
  | identifier as id              { NAME id }
  | eof                           { EOF }
  | _                             { failwith "Lexer error" }

and initial_linebegin = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline    { initial_linebegin lexbuf }
  | '#' | "%:"                    { hash lexbuf }
  | ""                            { initial lexbuf }

and char = parse
  | simple_escape_sequence        { let l = Lexing.lexeme lexbuf in
                                    let c = match l.[1] with 
                                    | 'a' -> '\007'
                                    | 'b' -> '\b'
                                    | 'f' -> '\012'
                                    | 'n' -> '\n'
                                    | 'r' -> '\r'
                                    | 't' -> '\t'
                                    | 'v' -> '\011'
                                    | c -> c in
                                    (c, l) }
  | octal_escape_sequence         { failwith "unsupported octal escape sequence" }
  | hexadecimal_escape_sequence   { let l = Lexing.lexeme lexbuf in
                                    let hex = String.sub l ~pos:2 ~len:(String.length l - 2) in
                                    match Char.of_int (Int.of_string ("0x" ^ hex)) with
                                    | Some c -> (c, l)
                                    | None -> failwith "unsupported hexadecimal escape sequence" }
  | universal_character_name      { failwith "unsupported universal character name" }
  | '\\' _                        { failwith "incorrect escape sequence" }
  | _                             { let l = Lexing.lexeme lexbuf in 
                                    let c = l.[0] in
                                    (c, l) }

and char_literal_end = parse
  | '\''       { }
  | '\n' | eof { failwith "missing terminating \"'\" character" }
  | ""         { ignore (char lexbuf); char_literal_end lexbuf }

and string_literal buf = parse
  | '\"'       { {value= Buffer.contents buf.value; literal= [Buffer.contents buf.literal]} }
  | '\n' | eof { failwith "missing terminating '\"' character" }
  | ""         { let (c, l) = char lexbuf in
                  Buffer.add_char buf.value c;
                  Buffer.add_string buf.literal l;
                  string_literal buf lexbuf }

and raw_string_literal buf = parse
  | '`'        { Buffer.contents buf }
  | '\n'       { Buffer.add_string buf "\n"; raw_string_literal buf lexbuf }
  | eof        { failwith "missing terminating \"`\" character" }
  | _          { let l = Lexing.lexeme lexbuf in
                  Buffer.add_string buf l;
                  raw_string_literal buf lexbuf }

(* We assume gcc -E syntax but try to tolerate variations. *)
and hash = parse
  | whitespace_char_no_newline+ digit* whitespace_char_no_newline*
    "\"" [^ '\n' '\"']* "\"" [^ '\n']* '\n'
  | whitespace_char_no_newline* "pragma"
    whitespace_char_no_newline+ [^ '\n']* '\n'
      { new_line lexbuf; initial_linebegin lexbuf }
  | [^ '\n']* eof
      { failwith "unexpected end of file" }
  | _
      { failwith "Lexer error" }

(* Multi-line comment terminated by "*/" *)
and multiline_comment = parse
  | "*/"   { () }
  | eof    { failwith "unterminated comment" }
  | '\n'   { new_line lexbuf; multiline_comment lexbuf }
  | _      { multiline_comment lexbuf }

(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | '\n'   { new_line lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }

{

  (* This lexer chooses between [inital] or [initial_linebegin],
     depending on whether we are at the beginning of the line or
     not. *)

  let lexer : lexbuf -> token =
    fun lexbuf ->
      if lexbuf.lex_curr_p.pos_cnum = lexbuf.lex_curr_p.pos_bol then
        initial_linebegin lexbuf
      else
        initial lexbuf

  (* In the following, we define a new lexer, which wraps [lexer], and applies
     the following two transformations to the token stream:

     - A [NAME] token is replaced with a sequence of either [NAME VARIABLE] or
       [NAME TYPE]. The decision is made via a call to [Context.is_typedefname].
       The call takes place only when the second element of the sequence is
       demanded.

     - When [Options.atomic_strict_syntax] is [true] and an opening parenthesis
       [LPAREN] follows an [ATOMIC] keyword, the parenthesis is replaced by a
       special token, [ATOMIC_LPAREN], so as to allow the parser to treat it
       specially. *)

  (* This second lexer is implemented using a 3-state state machine, whose
     states are as follows. *)

  type lexer_state =
    | SRegular          (* Nothing to recall from the previous tokens. *)
    | SAtomic           (* The previous token was [ATOMIC]. If an opening
                           parenthesis follows, then it needs special care. *)
    | SIdent of string  (* We have seen an identifier: we have just
                           emitted a [NAME] token. The next token will be
                           either [VARIABLE] or [TYPE], depending on
                           what kind of identifier this is. *)

  let lexer : lexbuf -> token =
    let st = ref SRegular in
    fun lexbuf ->
      match !st with

      | SIdent id ->
          st := SRegular;
          if is_typedefname id then TYPE else VARIABLE

      | SAtomic
      | SRegular ->
          let token = lexer lexbuf in
          match !st, token with
          | _, NAME id ->
              st := SIdent id;
              token

          | SAtomic, LPAREN ->
              st := SRegular;
              ATOMIC_LPAREN

          | _, ATOMIC ->
              st := (if !atomic_strict_syntax then SAtomic else SRegular);
              token

          | _, _ ->
              st := SRegular;
              token

}
