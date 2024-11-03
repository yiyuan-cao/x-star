module Ansi = struct
  (** Ansi terminal colors. *)

  open Core

  let make_color c = Printf.sprintf "\x1b[%dm%s\x1b[0m" c

  let black = make_color 30

  let red = make_color 31

  let green = make_color 32

  let yellow = make_color 33

  let blue = make_color 34

  let magenta = make_color 35

  let cyan = make_color 36

  let white = make_color 37

  let bright_black = make_color 90

  let bright_red = make_color 91

  let bright_green = make_color 92

  let bright_yellow = make_color 93

  let bright_blue = make_color 94

  let bright_magenta = make_color 95

  let bright_cyan = make_color 96

  let bright_white = make_color 97

  let strip_ansi s =
    let buffer = Buffer.create (String.length s) in
    let state = ref `Text in
    String.iter s ~f:(fun c ->
        let open Char in
        match !state with
        | `Text ->
            if c = '\x1b' then state := `Escape else Buffer.add_char buffer c
        | `Escape -> if c = '[' then state := `Bracket else state := `Text
        | `Bracket -> if is_digit c then state := `Digit else state := `Text
        | `Digit ->
            if is_digit c then ()
            else if c = 'm' then state := `Text
            else state := `Text ) ;
    Buffer.contents buffer

  let fprint channel s =
    let open Core_unix in
    let file = descr_of_out_channel channel in
    Printf.fprintf channel "%s" (if isatty file then s else strip_ansi s)
end

module Pretty = struct
  (** Pretty-printing combinators. *)

  open Core

  (** A pretty-printing document. *)
  type document = PPrint.document

  (** A palette of colors for syntax highlighting. *)
  type palette =
    { comment: string -> string
    ; keyword: string -> string
    ; literal: string -> string
    ; string: string -> string
    ; identifier: string -> string
    ; macro: string -> string
    ; class_: string -> string
    ; operator: string -> string
    ; symbol: string -> string
    ; type_: string -> string
    ; enum: string -> string }

  (** Pretty-printing configuration.

- [palette] is the palette of colors to use for syntax highlighting. If [None],
  no syntax highlighting is performed.
- [indent] is the number of spaces to use for indentation.
- [line_length] is the maximum number of characters per line.
*)
  type pretty_config =
    { mutable palette: palette option
    ; mutable indent: int
    ; mutable line_length: int }

  let config =
    { palette=
        Some
          { comment= Ansi.bright_black
          ; keyword= Ansi.blue
          ; literal= Ansi.cyan
          ; string= Ansi.yellow
          ; identifier= Ansi.white
          ; macro= Ansi.red
          ; class_= Ansi.green
          ; operator= Ansi.white
          ; symbol= Ansi.white
          ; type_= Ansi.green
          ; enum= Ansi.magenta }
    ; indent= 2
    ; line_length= 80 }

  (** An empty document. *)
  let empty = PPrint.empty

  (** A document containing a single space. *)
  let space = PPrint.space

  (** A forced line break. *)
  let hardline = PPrint.hardline

  (** [hardlines n] is [hardline] repeated [n] times. *)
  let hardlines n = PPrint.repeat n hardline

  (** [break] is a space if the line fits, otherwise a newline. *)
  let break = PPrint.break 1

  (** [softline] is nothing if the line fits, otherwise a newline. *)
  let softline = PPrint.break 0

  (** [group doc] tries to render [doc] on a single line, but if it does not
    fit, it will fall back to rendering it on multiple lines. *)
  let group = PPrint.group

  (** [flow docs] renders [docs] with spaces between them, and automatically
  inserts newlines if the line length is exceeded. *)
  let flow docs = PPrint.flow space docs

  (** [seperate sep docs] renders [docs] with [sep] in between. *)
  let seperate = PPrint.separate

  (** [seperate_map sep ~f docs] renders [f x] for each [x] in [docs], with [sep]
    in between. *)
  let seperate_map sep ~f docs = PPrint.separate_map sep f docs

  (** [optional ~f o] renders [f x] if [o] is [Some x], and nothing otherwise. *)
  let optional ~f o = PPrint.optional f o

  (** [a ^^ b] concatenates the documents [a] and [b]. *)
  let ( ^^ ) = PPrint.( ^^ )

  let colored get_color s =
    PPrint.fancystring
      ( config.palette
      |> Option.map ~f:(fun p -> get_color p s)
      |> Option.value ~default:s )
      (String.length s)

  (** [comment s] pretty-prints a comment. *)
  let comment = colored (fun p -> p.comment)

  (** [kwd s] pretty-prints a keyword. *)
  let kwd = colored (fun p -> p.keyword)

  (** [lit s] pretty-prints a literal. *)
  let lit = colored (fun p -> p.literal)

  (** [str s] pretty-prints a string. *)
  let str = colored (fun p -> p.string)

  (** [id s] pretty-prints an identifier. *)
  let id = colored (fun p -> p.identifier)

  (** [macro s] pretty-prints a macro. *)
  let macro = colored (fun p -> p.macro)

  (** [cls s] pretty-prints a class. *)
  let cls = colored (fun p -> p.class_)

  (** [op s] pretty-prints an operator. *)
  let op = colored (fun p -> p.operator)

  (** [sym s] pretty-prints a symbol. *)
  let sym = colored (fun p -> p.symbol)

  (** [ty s] pretty-prints a type. *)
  let ty = colored (fun p -> p.type_)

  (** [enum s] pretty-prints an enum. *)
  let enum = colored (fun p -> p.enum)

  (** [lit_int i] pretty-prints an integer literal. *)
  let lit_int i = lit (Int.to_string i)

  (** [nest doc] adds indentation at newlines. *)
  let nest doc = PPrint.nest config.indent doc

  (** [surround_parens opening content] renders [opening(content)]. *)
  let surround_parens opening contents =
    group (opening ^^ sym "(" ^^ (contents |> nest) ^^ sym ")")

  (** [surround_brackets opening content] renders [opening[content]]. *)
  let surround_brackets opening contents =
    group
      (opening ^^ sym "[" ^^ (break ^^ contents |> nest) ^^ break ^^ sym "]")

  (** [surround_braces opening content] renders [opening{content}]. *)
  let surround_braces opening contents =
    group
      (opening ^^ sym "{" ^^ (break ^^ contents |> nest) ^^ break ^^ sym "}")

  (** [surround_quotes q content] renders [content] surrounded by quote characters [q]. *)
  let surround_quotes q content = str q ^^ content ^^ str q

  (** [infix x op y] renders [x op y]. *)
  let infix x op y = flow [x; op; y]

  (** [prefix op x] renders [op x]. *)
  let prefix x y = group (x ^^ (break ^^ y |> nest))

  (** [comma] renders a comma. *)
  let comma = sym ","

  (** [semi] renders a semicolon. *)
  let semi = sym ";"

  (** [colon] renders a colon. *)
  let colon = sym ":"

  (** [dot] renders a dot. *)
  let dot = sym "."

  (** [comma_break] renders a comma followed by a line break. *)
  let comma_break = comma ^^ break

  (** [semi_break] renders a semicolon followed by a line break. *)
  let semi_break = semi ^^ break

  (** [parens x] renders [(x)]. *)
  let parens x = surround_parens empty x

  (** [brackets x] renders [[x]]. *)
  let brackets x = surround_brackets empty x

  (** [braces x] renders [{x}]. *)
  let braces x = surround_braces empty x
end

module Render = struct
  open Core

  (** Make a renderer for documents. *)
  module Make (R : PPrint.RENDERER with type document = PPrint.document) =
  struct
    (** [render doc output] renders [doc] to [output]. *)
    let render doc output = R.pretty 1. Pretty.config.line_length output doc
  end

  (** Render documents to channels, such as stdout. *)
  module ToChannel = Make (PPrint.ToChannel)

  (** Render documents to string buffers. *)
  module ToBuffer = Make (PPrint.ToBuffer)

  (** [doc_to_string printer doc] renders [doc] to a string. *)
  let render_to_string doc =
    let buf = Buffer.create 100 in
    ToBuffer.render doc buf ; Buffer.contents buf
end

open Core
open Ast
open Pretty

let rec program_to_doc program =
  (program |> List.map ~f:declaration_to_doc |> seperate (hardlines 2))
  ^^ hardline

and declaration_to_doc = function
  | Ddeffun _ as d -> declaration_to_doc_inner d
  | d -> declaration_to_doc_inner d ^^ semi

and declaration_to_doc_inner = function
  | Ddeclvar (typ, ident, init, _) ->
      parameter_to_doc (typ, ident)
      ^^ optional init ~f:(fun init ->
             space ^^ op "=" ^^ break ^^ init_to_doc init )
      |> nest |> group
  | Ddecltype (typ, _) -> typ_to_doc typ
  | Ddecltypedef (ident, typ, _) ->
      kwd "typedef" ^^ break ^^ parameter_to_doc (typ, ident)
      |> nest |> group
  | Ddeclfun (func, _) -> funsym_to_doc func
  | Ddeffun (func, _, stmt) ->
      funsym_to_doc func ^^ space ^^ stmt_to_doc stmt
  | Dattribute (attr, _) -> attribute_to_doc attr

and funsym_to_doc (typ, ident, params, _) =
  surround_parens (parameter_to_doc (typ, ident)) (parameters_to_doc params)

and stmt_to_doc = function
  | Sskip (attrs, _) -> attribute_list_to_doc attrs false ^^ semi |> group
  | Sblock (stmts, _) ->
      stmts |> List.map ~f:stmt_to_doc |> seperate break |> braces
  | Sexpr (expr, attrs, _) ->
      attribute_list_to_doc attrs true ^^ expr_to_doc expr ^^ semi |> group
  | Sif (expr, then_stmt, else_stmt, attrs, _) ->
      let cond = surround_parens (kwd "if" ^^ space) (expr_to_doc expr) in
      let then_stmt =
        match then_stmt with
        | Sblock _ -> space ^^ stmt_to_doc then_stmt
        | _ -> break ^^ stmt_to_doc then_stmt |> nest
      in
      let else_stmt =
        match else_stmt with
        | Some (Sblock _ as else_stmt) ->
            break ^^ kwd "else" ^^ space ^^ stmt_to_doc else_stmt
        | Some _ ->
            break ^^ kwd "else"
            ^^ (break ^^ stmt_to_doc (Option.value_exn else_stmt) |> nest)
        | None -> empty
      in
      attribute_list_to_doc attrs true ^^ cond ^^ then_stmt ^^ else_stmt
      |> group
  | Swhile (expr, stmt, attrs, _) ->
      let cond = surround_parens (kwd "while" ^^ space) (expr_to_doc expr) in
      let doc =
        match stmt with
        | Sblock _ -> cond ^^ space ^^ stmt_to_doc stmt
        | _ -> prefix cond (stmt_to_doc stmt)
      in
      attribute_list_to_doc attrs true ^^ doc |> group
  | Sbreak _ -> kwd "break" ^^ semi
  | Scontinue _ -> kwd "continue" ^^ semi
  | Sreturn (None, _) -> kwd "return" ^^ semi
  | Sreturn (Some expr, _) ->
      kwd "return" ^^ space ^^ expr_to_doc expr ^^ semi
  | Sdecl (decl, attrs) ->
      attribute_list_to_doc attrs true ^^ declaration_to_doc decl

and init_to_doc = function
  | Init_single e -> expr_to_doc e
  | Init_array l -> braces (seperate_map comma_break ~f:init_to_doc l)
  | Init_struct l ->
      braces
        (seperate_map comma_break
           ~f:(fun (i, init) ->
             sym "." ^^ id i ^^ space ^^ op "=" ^^ break ^^ init_to_doc init )
           l )

(* The expression unparsing algorithm is from:
    Ramsey, N. (1998). Unparsing expressions with prefix and postfix operators.
    Software: Practice and Experience, 28(12), 1327-1356. *)

and expr_to_doc e =
  let no_parens (pi, ai) (po, ao) side =
    pi < po || Stdlib.(pi == po && ai = ao && ai = side)
  in
  let bracket (inner, subexpr) side outer =
    if no_parens inner outer side then subexpr else parens subexpr
  in
  let rec unparse = function
    | Econst c -> ((0, `NonAssoc), constant_to_doc c)
    | Evar i -> ((0, `NonAssoc), id i)
    | Ebackquoted s -> ((0, `NonAssoc), surround_quotes "`" (str s))
    | Ecomplit (t, i) ->
        let prec = (1, `LeftAssoc) in
        let doc = surround_braces (parens (typ_to_doc t)) (init_to_doc i) in
        (prec, doc)
    | Eunary (op, e) ->
        let prec =
          match op with
          | Ominus | Oplus | Olognot | Obitneg | Oderef | Oaddrof ->
              (2, `RightAssoc)
          | Odot _ | Oarrow _ -> (1, `LeftAssoc)
        in
        let doc = bracket (unparse e) (snd prec) prec in
        (prec, unary_operator_expr_to_doc doc op)
    | Ebinary (Oindex, e1, e2) ->
        let prec = (1, `LeftAssoc) in
        let l = bracket (unparse e1) `LeftAssoc prec
        and r = bracket (unparse e2) `LeftAssoc (15, `NonAssoc) in
        (prec, surround_brackets l r)
    | Ebinary (op, e1, e2) ->
        let prec =
          match op with
          | Oindex -> failwith "[Oindex] should be handled elsewhere"
          | Omul | Odiv | Omod -> (3, `LeftAssoc)
          | Oadd | Osub -> (4, `LeftAssoc)
          | Obitrsh | Obitlsh -> (5, `LeftAssoc)
          | Olt | Ogt | Ole | Oge -> (6, `LeftAssoc)
          | Oeq | One -> (7, `LeftAssoc)
          | Obitand -> (8, `LeftAssoc)
          | Obitxor -> (9, `LeftAssoc)
          | Obitor -> (10, `LeftAssoc)
          | Ologand | Osep | Osepand -> (11, `LeftAssoc)
          | Ologor -> (12, `LeftAssoc)
          | Oassign -> (14, `RightAssoc)
          | Ocomma -> (15, `NonAssoc)
        in
        let l = bracket (unparse e1) `LeftAssoc prec
        and r = bracket (unparse e2) `RightAssoc prec in
        (prec, binary_operator_expr_to_doc l r op)
    | Ecall (e, args) ->
        let prec = (1, `LeftAssoc) in
        let e = bracket (unparse e) `LeftAssoc prec in
        let doc_args =
          seperate_map comma_break
            ~f:(fun e -> bracket (unparse e) `LeftAssoc (15, `NonAssoc))
            args
        in
        (prec, surround_parens e doc_args)
    | Esizeofexpr e ->
        let prec = (2, `NonAssoc) in
        let doc = bracket (unparse e) `LeftAssoc (15, `NonAssoc) in
        (prec, surround_parens (kwd "sizeof") doc)
    | Esizeoftyp t ->
        let prec = (2, `NonAssoc) in
        let doc = typ_to_doc t in
        (prec, surround_parens (kwd "sizeof") doc)
    | Ecast (t, e) ->
        let prec = (2, `NonAssoc) in
        let doc = bracket (unparse e) `LeftAssoc prec in
        (prec, parens (typ_to_doc t) ^^ doc)
    | Econditional (e1, e2, e3) ->
        let prec = (13, `RightAssoc) in
        let doc1 = bracket (unparse e1) `LeftAssoc prec
        and doc2 = bracket (unparse e2) `LeftAssoc (16, `NonAssoc)
        and doc3 = bracket (unparse e3) `RightAssoc prec in
        (prec, flow [doc1; op "?"; doc2; op ":"; doc3])
    | Elet_data_at (e, t, i) ->
        let prec = (1, `LeftAssoc) in
        let d = bracket (unparse e) `LeftAssoc (15, `NonAssoc) in
        let spec, decl = declarator_to_doc t (id i) in
        let doc =
          surround_parens (kwd "LET_DATA_AT") (flow [d ^^ comma; spec; decl])
        in
        (prec, doc)
  in
  unparse e |> snd

and backquoted_expr_to_doc_impl _ = function _ -> empty

and unary_operator_expr_to_doc doc = function
  | Ominus -> op "-" ^^ doc
  | Oplus -> op "+" ^^ doc
  | Olognot -> op "!" ^^ doc
  | Obitneg -> op "~" ^^ doc
  | Oderef -> op "*" ^^ doc
  | Oaddrof -> op "&" ^^ doc
  | Odot i -> doc ^^ op "." ^^ id i
  | Oarrow i -> doc ^^ op "->" ^^ id i

and binary_operator_expr_to_doc d1 d2 = function
  | Omul -> infix d1 (op "*") d2
  | Odiv -> infix d1 (op "/") d2
  | Omod -> infix d1 (op "%") d2
  | Oadd -> infix d1 (op "+") d2
  | Osub -> infix d1 (op "-") d2
  | Olt -> infix d1 (op "<") d2
  | Ogt -> infix d1 (op ">") d2
  | Ole -> infix d1 (op "<=") d2
  | Oge -> infix d1 (op ">=") d2
  | Oeq -> infix d1 (op "==") d2
  | One -> infix d1 (op "!=") d2
  | Oindex -> surround_brackets d1 d2
  | Ologand -> infix d1 (op "&&") d2
  | Ologor -> infix d1 (op "||") d2
  | Osep -> infix d1 (op "SEP") d2
  | Osepand -> infix d1 (op "SEPAND") d2
  | Obitand -> infix d1 (op "&") d2
  | Obitxor -> infix d1 (op "^") d2
  | Obitor -> infix d1 (op "|") d2
  | Obitlsh -> infix d1 (op "<<") d2
  | Obitrsh -> infix d1 (op ">>") d2
  | Oassign -> infix d1 (op "=") d2
  | Ocomma -> d1 ^^ comma ^^ break ^^ d2

and declarator_to_doc t i =
  match t with
  | Tvoid -> (ty "void", i)
  | T_Bool -> (ty "_Bool", i)
  | Tchar -> (ty "char", i)
  | Tuchar -> (ty "unsigned char", i)
  | Tint -> (ty "int", i)
  | Tuint -> (ty "unsigned int", i)
  | Tlong -> (ty "long", i)
  | Tulong -> (ty "unsigned long", i)
  | Tprop -> (ty "PROP", i)
  | Thprop -> (ty "HPROP", i)
  | Tptr t ->
      let spec, decl = declarator_to_doc t i in
      (spec, sym "*" ^^ decl)
  | Tarray (t, None) ->
      let spec, decl = declarator_to_doc t i in
      (spec, decl ^^ op "[]")
  | Tarray (t, Some c) ->
      let spec, decl = declarator_to_doc t i in
      (spec, decl ^^ op "[" ^^ expr_to_doc c.expr ^^ op "]")
  | Tstruct name -> (kwd "struct" ^^ space ^^ id name, i)
  | Tunion name -> (kwd "union" ^^ space ^^ id name, i)
  | Tnamed name -> (id name, i)
  | Tstructdecl (name, fields) ->
      let fields_doc = fields_to_doc fields in
      let spec =
        kwd "struct" ^^ optional name ~f:(fun i -> space ^^ id i) ^^ space
      in
      (surround_braces spec fields_doc, i)
  | Tuniondecl (name, fields) ->
      let fields_doc = fields_to_doc fields in
      let spec =
        kwd "union " ^^ optional name ~f:(fun i -> space ^^ id i) ^^ space
      in
      (surround_braces spec fields_doc, i)

and typ_to_doc t =
  let spec, decl = declarator_to_doc t (id "") in
  spec ^^ decl

and field_to_doc f = parameter_to_doc f ^^ semi

and fields_to_doc fs = seperate_map break ~f:field_to_doc fs

and parameter_to_doc (t, i) =
  let spec, decl = declarator_to_doc t (id i) in
  spec ^^ break ^^ decl

and parameters_to_doc ps = seperate_map comma_break ~f:parameter_to_doc ps

and constant_to_doc = function
  | Cinteger i -> lit_int i
  | Cboolean b -> if b then kwd "true" else kwd "false"
  | Cstring s ->
      seperate_map empty s.literal ~f:(fun s -> surround_quotes "\"" (str s))
  | Cquoted s -> surround_quotes "`" (str s)
  | Cnullval -> expr_to_doc (Econst (Cinteger 0))

and attribute_list_to_doc attrs follow_break =
  if List.is_empty attrs then empty
  else
    seperate_map break ~f:attribute_to_doc attrs
    ^^ if follow_break then break else empty

and attribute_to_doc = function
  | Acstar attr ->
      let name, inner = cstar_attribute_to_doc attr in
      sym "[["
      ^^ surround_parens (kwd name) (softline ^^ inner ^^ softline |> group)
      ^^ sym "]]"

and cstar_attribute_to_doc = function
  | Afunction f -> ("cstar::function", declaration_to_doc_inner f)
  | Arepresentation r -> ("cstar::representation", declaration_to_doc_inner r)
  | Apredicate p -> ("cstar::predicate", declaration_to_doc_inner p)
  | Adatatype d -> ("cstar::datatype", cstar_datatype_to_doc d)
  | Aparameter p -> ("cstar::parameter", expr_to_doc p)
  | Arequire r -> ("cstar::require", expr_to_doc r)
  | Aensure e -> ("cstar::ensure", expr_to_doc e)
  | Aassert a -> ("cstar::assert", expr_to_doc a)
  | Aghostvar v -> ("cstar::ghostvar", declaration_to_doc_inner v)
  | Ainvariant i -> ("cstar::invariant", expr_to_doc i)
  | Aproof ss ->
      let stmts = ss |> List.map ~f:stmt_to_doc |> seperate break in
      ("cstar::proof", stmts)
  | Atype t -> ("cstar::type", expr_to_doc t)
  | Aargument a ->
      ("cstar::argument", seperate_map comma_break ~f:expr_to_doc a)

and cstar_datatype_to_doc {name; constructors} =
  let name_doc = id name in
  let constructors_doc =
    constructors
    |> seperate_map comma_break ~f:(fun (i, params) ->
           surround_parens (id i) (parameters_to_doc params) )
  in
  name_doc ^^ comma_break ^^ constructors_doc |> nest |> group
