(* -------------------------------------------------------------------- *)
open Utils

type token = Parser.token =
  | WHILE
  | UNDERSCORE
  | UNALIGNED
  | T_W of (Syntax.swsize)
  | T_INT_CAST of (Syntax.sign)
  | T_INT
  | T_BOOL
  | TYPE
  | TRUE
  | TO
  | SWSIZE of (Syntax.swsize)
  | SVSIZE of (Syntax.svsize)
  | STRING of (string)
  | STAR
  | STACK
  | SLASH of (Syntax.sign option)
  | SHARPLBRACKET
  | SHARP
  | SEMICOLON
  | RPAREN
  | ROR
  | ROL
  | RETURN
  | REQUIRE
  | REG
  | RBRACKET
  | RBRACE
  | RARROW
  | QUESTIONMARK
  | POINTER
  | PLUS
  | PIPEPIPE
  | PIPE
  | PERCENT of (Syntax.sign option)
  | PARAM
  | NID of (string)
  | NAMESPACE
  | MUTABLE
  | MINUS
  | LTLT
  | LT of (Syntax.sign option)
  | LPAREN
  | LE of (Syntax.sign option)
  | LBRACKET
  | LBRACE
  | INT of (Syntax.int_representation)
  | INLINE
  | IF
  | HAT
  | GTGT of (Syntax.sign option)
  | GT of (Syntax.sign option)
  | GLOBAL
  | GE of (Syntax.sign option)
  | FROM
  | FOR
  | FN
  | FALSE
  | EXPORT
  | EXEC
  | ERROR_TOKEN of (Mastic.Error.t)
  | EQEQ
  | EQ
  | EOF
  | ELSE
  | DOWNTO
  | DOT
  | CONSTANT
  | COMMA
  | COLONCOLON
  | COLON
  | BANGEQ
  | BANG
  | ASSERT
  | ARRAYINIT
  | AMPAMP
  | AMP
  | ALIGNED
  [@@deriving show]

(* A short name for the incremental parser API. *)
module I = Parser.MenhirInterpreter

let show_terminal : type a. a I.terminal -> string = function
  | T_error -> "err"
  | T_WHILE -> "while"
  | T_UNDERSCORE -> "_"
  | T_UNALIGNED -> "#unaligned"
  | T_T_W -> "<wordtype>"
  | T_T_INT_CAST -> "<intcast>"
  | T_T_INT -> "int"
  | T_T_BOOL -> "bool"
  | T_TYPE -> "type"
  | T_TRUE -> "true"
  | T_TO -> "to"
  | T_SWSIZE -> "<swsize>"
  | T_SVSIZE -> "svsize"
  | T_STRING -> "<string>"
  | T_STAR -> "*"
  | T_STACK -> "stack"
  | T_SLASH -> "/"
  | T_SHARPLBRACKET -> "#["
  | T_SHARP -> "#"
  | T_SEMICOLON -> ";"
  | T_RPAREN -> ")"
  | T_ROR -> ">>r"
  | T_ROL -> "<<r"
  | T_RETURN -> "return"
  | T_REQUIRE -> "require"
  | T_REG -> "reg"
  | T_RBRACKET -> "]"
  | T_RBRACE -> "}"
  | T_RARROW -> "->"
  | T_QUESTIONMARK -> "?"
  | T_POINTER -> "ptr"
  | T_PLUS -> "+"
  | T_PIPEPIPE -> "||"
  | T_PIPE -> "|"
  | T_PERCENT -> "%"
  | T_PARAM -> "param"
  | T_NID -> "<NID>"
  | T_NAMESPACE -> "namespace"
  | T_MUTABLE -> "mut"
  | T_MINUS -> "-"
  | T_LTLT -> "<<"
  | T_LT -> "<"
  | T_LPAREN -> "("
  | T_LE -> "<="
  | T_LBRACKET -> "["
  | T_LBRACE -> "{"
  | T_INT -> "<int>"
  | T_INLINE -> "inline"
  | T_IF -> "if"
  | T_HAT -> "^"
  | T_GTGT -> ">>"
  | T_GT -> ">"
  | T_GLOBAL -> "global"
  | T_GE -> ">="
  | T_FROM -> "from"
  | T_FOR -> "for"
  | T_FN -> "fn"
  | T_FALSE -> "false"
  | T_EXPORT -> "export"
  | T_EXEC -> "exec"
  | T_ERROR_TOKEN -> "perr"
  | T_EQEQ -> "=="
  | T_EQ -> "="
  | T_EOF -> "eof"
  | T_ELSE -> "else"
  | T_DOWNTO -> "downto"
  | T_DOT -> "."
  | T_CONSTANT -> "const"
  | T_COMMA -> ","
  | T_COLONCOLON -> "::"
  | T_COLON -> ":"
  | T_BANGEQ -> "!="
  | T_BANG -> "!"
  | T_ASSERT -> "assert"
  | T_ARRAYINIT -> "ArrayInit"
  | T_AMPAMP -> "&&"
  | T_AMP -> "&"
  | T_ALIGNED -> "#aligned"

let show_nonterminal : type a. a I.nonterminal -> string = function
  | N_writable -> "<writable>"
  | N_var -> "<var>"
  | N_utype_array -> "<array type>"
  | N_utype -> "<utype>"
  | N_top_annotation -> "<annotation>"
  | N_top -> "<toplevel>"
  | N_swsize -> "<swsize>"
  | N_svsize -> "<svsize>"
  | N_struct_annot -> "<annotation>"
  | N_storage -> "<storage>"
  | N_stor_type -> "<storage + type>"
  | N_simple_attribute -> "<simple attribute>"
  | N_loption_separated_nonempty_list_COMMA_pexpr_noarr__ -> "???"
  | N_separated_nonempty_list_option_COMMA__var_ -> "<list of vars>"
  | N_separated_nonempty_list_empty_var_ -> "???"
  | N_separated_nonempty_list_COMMA_var_ -> "???"
  | N_separated_nonempty_list_COMMA_range_ -> "???"
  | N_separated_nonempty_list_COMMA_plvalue_ -> "???"
  | N_separated_nonempty_list_COMMA_pexpr_ -> "???"
  | N_separated_nonempty_list_COMMA_pexpr_noarr_ -> "???"
  | N_separated_nonempty_list_COMMA_loc_decl__ -> "???"
  | N_separated_nonempty_list_COMMA_annotation_ -> "???"
  | N_separated_nonempty_list_COMMA_annot_stor_type_ -> "???"
  | N_separated_nonempty_list_COMMA_annot_pparamdecl_ -> "???"
  | N_separated_nonempty_list_COLONCOLON_NID_ -> "???"
  | N_range -> "<range>"
  | N_ptype_r -> "<type>"
  | N_ptype -> "<type>"
  | N_ptr -> "???"
  | N_prim -> "???"
  | N_prequire1 -> "???"
  | N_prequire -> "???"
  | N_pparamdecl_empty_ -> "???"
  | N_pparam -> "???"
  | N_pointer -> "???"
  | N_plvalues -> "???"
  | N_plvalue_r -> "???"
  | N_plvalue -> "???"
  | N_pinstr_r -> "???"
  | N_pinstr -> "???"
  | N_pif -> "???"
  | N_pglobal -> "???"
  | N_pgexpr -> "???"
  | N_pfundef -> "???"
  | N_pfunbody -> "???"
  | N_pexpr_noarr_r_pexpr_noarr_ -> "???"
  | N_pexpr_noarr_r_pexpr_ -> "???"
  | N_pexpr_noarr -> "???"
  | N_pexpr_r -> "???"
  | N_pexpr -> "???"
  | N_pexec -> "???"
  | N_peqop -> "???"
  | N_pelseif -> "???"
  | N_pelse -> "???"
  | N_pblock_r -> "???"
  | N_pblock -> "???"
  | N_option_writable_ -> "???"
  | N_option_unaligned_ -> "???"
  | N_option_prefix_RARROW_tuple_annot_stor_type___ -> "???"
  | N_option_prefix_IF_pexpr__ -> "???"
  | N_option_pointer_ -> "???"
  | N_option_pblock_ -> "???"
  | N_option_loc_castop1__ -> "???"
  | N_option_from_ -> "???"
  | N_option_call_conv_ -> "???"
  | N_option_attribute_ -> "???"
  | N_option_arr_access_len_ -> "???"
  | N_option_access_type_ -> "???"
  | N_option___anonymous_1_ -> "???"
  | N_option_DOT_ -> "???"
  | N_option_COMMA_ -> "???"
  | N_option_COLON_ -> "???"
  | N_nonempty_list_prequire1_ -> "???"
  | N_module_ -> "???"
  | N_loption_separated_nonempty_list_COMMA_var__ -> "???"
  | N_loption_separated_nonempty_list_COMMA_range__ -> "???"
  | N_loption_separated_nonempty_list_COMMA_pexpr__ -> "???"
  | N_loption_separated_nonempty_list_COMMA_annotation__ -> "???"
  | N_loption_separated_nonempty_list_COMMA_annot_stor_type__ -> "???"
  | N_loption_separated_nonempty_list_COMMA_annot_pparamdecl__ -> "???"
  | N_list_top_annotation_ -> "???"
  | N_list_pinstr_ -> "???"
  | N_list_loc_top__ -> "???"
  | N_keyword -> "???"
  | N_implicites -> "???"
  | N_from -> "???"
  | N_castop1 -> "???"
  | N_castop -> "???"
  | N_cast -> "???"
  | N_call_conv -> "???"
  | N_attribute -> "???"
  | N_arr_access_len -> "???"
  | N_arr_access_i -> "???"
  | N_arr_access -> "???"
  | N_annotations -> "???"
  | N_annotationlabel -> "???"
  | N_annotation -> "???"
  | N_annot_stor_type -> "???"
  | N_annot_pparamdecl -> "???"

let pp_symbol : type a. a option -> Format.formatter -> a I.symbol -> unit =
  fun x fmt s ->
    match s with
    | I.N nt ->
        begin match x with
        | None -> Format.fprintf fmt "%s" (show_nonterminal nt)
        | Some _x -> Format.fprintf fmt "call printer there"
        end
    | I.T t ->
        Format.fprintf fmt "%s" (show_terminal t)

let token_of_terminal : type a. a I.terminal -> (string * token) option = function
  | T_error -> assert false
  | T_WHILE -> Some ("while", WHILE)
  | T_UNDERSCORE -> Some ("_", UNDERSCORE)
  | T_UNALIGNED -> Some ("#unaligned", UNALIGNED)
  | T_T_W -> None
  | T_T_INT_CAST -> None
  | T_T_INT -> Some ("int", T_INT)
  | T_T_BOOL -> Some ("bool", T_BOOL)
  | T_TYPE -> Some ("type", TYPE)
  | T_TRUE -> Some ("true", TRUE)
  | T_TO -> Some ("to", TO)
  | T_SWSIZE -> None
  | T_SVSIZE -> None
  | T_STRING -> None
  | T_STAR -> Some ("*", STAR)
  | T_STACK -> Some ("stack", STACK)
  | T_SLASH -> None
  | T_SHARPLBRACKET -> Some ("#[", SHARPLBRACKET)
  | T_SHARP -> Some ("#", SHARP)
  | T_SEMICOLON -> Some (";", SEMICOLON)
  | T_RPAREN -> Some (")", RPAREN)
  | T_ROR -> Some (">>r", ROR)
  | T_ROL -> Some ("<<r", ROL)
  | T_RETURN -> Some ("return", RETURN)
  | T_REQUIRE -> Some ("require", REQUIRE)
  | T_REG -> Some ("reg", REG)
  | T_RBRACKET -> Some ("]", RBRACKET)
  | T_RBRACE -> Some ("}", RBRACE)
  | T_RARROW -> Some ("->", RARROW)
  | T_QUESTIONMARK -> Some ("?", QUESTIONMARK)
  | T_POINTER -> Some ("ptr", POINTER)
  | T_PLUS -> Some ("+", PLUS)
  | T_PIPEPIPE -> Some ("||", PIPEPIPE)
  | T_PIPE -> Some ("|", PIPE)
  | T_PERCENT -> None
  | T_PARAM -> Some ("param", PARAM)
  | T_NID -> None
  | T_NAMESPACE -> Some ("namespace", NAMESPACE)
  | T_MUTABLE -> Some ("mut", MUTABLE)
  | T_MINUS -> Some ("-", MINUS)
  | T_LTLT -> Some ("<<", LTLT)
  | T_LT -> None
  | T_LPAREN -> Some ("(", LPAREN)
  | T_LE -> None
  | T_LBRACKET -> Some ("[", LBRACKET)
  | T_LBRACE -> Some ("{", LBRACE)
  | T_INT -> None
  | T_INLINE -> Some ("inline", INLINE)
  | T_IF -> Some ("if", IF)
  | T_HAT -> Some ("^", HAT)
  | T_GTGT -> None
  | T_GT -> None
  | T_GLOBAL -> Some ("global", GLOBAL)
  | T_GE -> None
  | T_FROM -> Some ("from", FROM)
  | T_FOR -> Some ("for", FOR)
  | T_FN -> Some ("fn", FN)
  | T_FALSE -> Some ("false", FALSE)
  | T_EXPORT -> Some ("export", EXPORT)
  | T_EXEC -> Some ("exec", EXEC)
  | T_ERROR_TOKEN -> None
  | T_EQEQ -> Some ("==", EQEQ)
  | T_EQ -> Some ("=", EQ)
  | T_EOF -> Some ("eof", EOF)
  | T_ELSE -> Some ("else", ELSE)
  | T_DOWNTO -> Some ("downto", DOWNTO)
  | T_DOT -> Some (".", DOT)
  | T_CONSTANT -> Some ("const", CONSTANT)
  | T_COMMA -> Some (",", COMMA)
  | T_COLONCOLON -> Some ("::", COLONCOLON)
  | T_COLON -> Some (":", COLON)
  | T_BANGEQ -> Some ("!=", BANGEQ)
  | T_BANG -> Some ("!", BANG)
  | T_ASSERT -> Some ("assert", ASSERT)
  | T_ARRAYINIT -> Some ("ArrayInit", ARRAYINIT)
  | T_AMPAMP -> Some ("&&", AMPAMP)
  | T_AMP -> Some ("&", AMP)
  | T_ALIGNED -> Some ("#aligned", ALIGNED)

module IncrementalParser = struct
  type 'a checkpoint = 'a I.checkpoint
  type ast = Syntax.pprogram

  let main = Parser.Incremental.module_

  type token = I.token

  let token = Lexer.main
end

module Recovery = struct
  type token = I.token

  let show_token = show_token

  type 'a symbol = 'a I.symbol
  type xsymbol = I.xsymbol

  let pp_symbol = pp_symbol

  type 'a terminal = 'a I.terminal
  type 'a env = 'a I.env
  type production = I.production

  let token_of_terminal = token_of_terminal
  let match_error_token = function ERROR_TOKEN x -> Some x | _ -> None
  let build_error_token t = ERROR_TOKEN t

  (* Initialize the lexer, and catch any exception raised by the lexer. *)
  let handle_unexpected_token ~productions:_ ~next_token:tok ~acceptable_tokens ~reducible_productions:prods
      ~generation_streak =
    let open Mastic.ErrorResilientParser in
    if prods <> [] then Reduce (List.hd prods)
    else
      match tok with
      (* tokens that look like a good point to re-start parsing (or terminate).
       these are typically the reserved words (keywords) of the language *)
      | { t = FN | INLINE | EXPORT | PARAM } -> begin
          match prods with
          | p :: _ ->
              (* if we can reduce we do it. it could be we are parsing something
               optional for example, but the next token is not a lookahead we exepct *)
              Reduce p
          | [] -> (
                (* we try to complete one of the current productions *)
                match acceptable_tokens with
                | x :: _ ->
                    (* this is a token that makes the automaton shift *)
                    if generation_streak < 10 then GenerateToken x else TurnIntoError
                | [] ->
                    (* if we are parsing the top level production there is not point in padding
                   TODO: maybe all list(something) should do the same *)
                    if generation_streak >= 10 then TurnIntoError
                    else GenerateHole (* this is a hole, the error production for the current nonterminal *))
        end
      | _ -> TurnIntoError

  let reduce_as_parse_error : type a. a -> a I.symbol -> Lexing.position -> Lexing.position -> token =
   fun x tx b e ->
    match tx with
    | I.N I.N_module_ -> assert false
    | I.N I.N_pfundef -> ERROR_TOKEN (Syntax.build_token (Mastic.Error.loc (Syntax.PFundef x) b e))
    | I.N I.N_pparam -> ERROR_TOKEN (Syntax.build_token (Mastic.Error.loc (Syntax.PParam x) b e))
    | I.N I.N_pglobal -> ERROR_TOKEN (Syntax.build_token (Mastic.Error.loc (Syntax.PGlobal x) b e))
    | I.N I.N_pexec -> ERROR_TOKEN (Syntax.build_token (Mastic.Error.loc (Syntax.Pexec x) b e))
    | I.N I.N_prequire -> ERROR_TOKEN (Syntax.build_token (Mastic.Error.loc (Syntax.Prequire x) b e))
    | _ -> ERROR_TOKEN Mastic.Error.(mkLexError (loc (Format.asprintf "%a" (pp_symbol (Some x)) tx) b e))

  let is_eof_token = function EOF -> true | _ -> false
end

module ERParser = Mastic.ErrorResilientParser.Make (I) (IncrementalParser) (Recovery)

(* -------------------------------------------------------------------- *)
let lexbuf_from_function = fun name f ->
  let lexbuf = Lexing.from_function f in
  Lexing.set_filename lexbuf name;
  lexbuf

(* -------------------------------------------------------------------- *)
let pp_position fmt pos =
  let open Lexing in
  Format.fprintf fmt "in file %s, at line %d, at character %d"
    pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol)

let pp_ex_token fmt (pos, s) =
  Format.fprintf fmt "at %a: %s" pp_position pos s

let parse_program ?(name = "") (inc : IO.input) =
  let lexbuf = lexbuf_from_function name @@ fun buf n ->
  try IO.input inc buf 0 n with IO.No_more_input -> 0 in
  let _, extra_tokens, ast = ERParser.parse lexbuf in
  Format.eprintf "extra_tokens: @[<v>%a@]@." (pp_list "@," pp_ex_token) extra_tokens;
  ast
