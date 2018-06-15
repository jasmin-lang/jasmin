{
  open Utils
  open Parser

  module L = Location
  module S = Syntax

  let unterminated_comment loc =
    raise (S.ParseError (loc, Some "unterminated comment"))

  let invalid_char loc (c : char) =
    let msg = Printf.sprintf "invalid char: `%c'" c in
    raise (S.ParseError (loc, Some msg))

  let _keywords = [
    "u8"    , T_U8   ;
    "u16"   , T_U16  ;
    "u32"   , T_U32  ;
    "u64"   , T_U64  ;
    "u128"  , T_U128 ;
    "u256"  , T_U256 ;

    "bool"  , T_BOOL ;
    "int"   , T_INT  ;

    "downto", DOWNTO ;
    "else"  , ELSE   ;
    "false" , FALSE  ;
    "fn"    , FN     ;
    "for"   , FOR    ;
    "global", GLOBAL ;
    "if"    , IF     ;
    "inline", INLINE ;
    "param" , PARAM  ;
    "reg"   , REG    ;
    "return", RETURN ;
    "stack" , STACK  ;
    "to"    , TO     ;
    "true"  , TRUE   ;
    "while" , WHILE  ;
    "export", EXPORT ;
    "ArrayInit", ARRAYINIT;
    "_"     , UNDERSCORE;
  ]

  let keywords = Hash.of_enum (List.enum _keywords)

  let sign_of_char =
  function
  | 'u' -> `Unsigned
  | 's' -> `Signed
  | _ -> assert false

  let get_sign : char option -> S.sign option =
  function
  | Some c -> Some (sign_of_char c)
  | None -> None

  let size_of_string =
  function
  | "8" -> `W8
  | "16" -> `W16
  | "32" -> `W32
  | "64" -> `W64
  | "128" -> `W128
  | "256" -> `W256
  | _ -> assert false

  let get_size : string option -> S.wsize option =
  function
  | Some s -> Some (size_of_string s)
  | None -> None

  let mk_swsize g w : S.swsize =
    match get_sign g, get_size w with
    | Some g, (Some _ as w) -> Some (g, w)
    | None, None -> None
    | _, _ -> assert false
}

(* -------------------------------------------------------------------- *)
let blank    = [' ' '\t' '\r']
let newline  = ['\n']
let digit    = ['0'-'9']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']
let lower    = ['a'-'z']
let upper    = ['A'-'Z']
let letter   = (lower | upper)
let idletter = letter | '_'
let ident    = idletter (idletter | digit)*

let size = "8" | "16" | "32" | "64" | "128" | "256"
let signletter = ['s' 'u']

(* -------------------------------------------------------------------- *)
rule main = parse
  | newline { Lexing.new_line lexbuf; main lexbuf }
  | blank+  { main lexbuf }

  | "/*" { comment 0 lexbuf; main lexbuf }

  | "//" [^'\n']* newline { Lexing.new_line lexbuf; main lexbuf }
  | "//" [^'\n']* eof     { main lexbuf }

  | ('-'? digit+) as s
      { INT (Bigint.of_string s) }

  | ("0x" hexdigit+) as s
      { INT (Bigint.of_string s) }

  | ident+ as s
      { odfl (NID s) (Hash.find_option keywords s) }

  | '(' blank* (size as sz) (signletter as sg) blank* ')' { CAST (sign_of_char sg, size_of_string sz) }

  | "#"     { SHARP      }
  | "["     { LBRACKET   }
  | "]"     { RBRACKET   }
  | "{"     { LBRACE     }
  | "}"     { RBRACE     }
  | "("     { LPAREN     }
  | ")"     { RPAREN     }
  | "->"    { RARROW     }
  | ","     { COMMA      }
  | ";"     { SEMICOLON  }
  | "?"     { QUESTIONMARK  }
  | ":"     { COLON  }

  | "<<" (blank* (size as w) (signletter as g))? { LTLT (mk_swsize g w) }
  | "<=s" { LE (Some (`Signed, None)) }
  | "<=" (blank* (size as w) (signletter as g))? { LE (mk_swsize g w) }
  | "<s" { LT (Some (`Signed, None)) }
  | "<" (blank* (size as w) (signletter as g))? { LT (mk_swsize g w) }

  | ">>" (blank* (size as w) (signletter as g))? { GTGT (mk_swsize g w) }
  | ">>s" { GTGT (Some (`Signed, None)) }
  | ">=s" { GE (Some (`Signed, None)) }
  | ">=" (blank* (size as w) (signletter as g))? { GE (mk_swsize g w) }
  | ">s" { GT (Some (`Signed, None)) }
  | ">" (blank* (size as w) (signletter as g))? { GT (mk_swsize g w) }

  | "!" (blank* (size as w) (signletter as g))? { BANG (mk_swsize g w) }
  | "+" (blank* (size as w) (signletter as g))? { PLUS (mk_swsize g w) }
  | "-" (blank* (size as w) (signletter as g))? { MINUS (mk_swsize g w) }
  | "*" (blank* (size as w) (signletter as g))? { STAR (mk_swsize g w) }
  | "/" (blank* (size as w) (signletter as g))? { SLASH (mk_swsize g w) }
  | "%" (blank* (size as w) (signletter as g))? { PERCENT (mk_swsize g w) }
  | "|" (blank* (size as w) (signletter as g))? { PIPE (mk_swsize g w) }
  | "&" (blank* (size as w) (signletter as g))? { AMP (mk_swsize g w) }
  | "^" (blank* (size as w) (signletter as g))? { HAT (mk_swsize g w) }
  | "&&"    { AMPAMP     }
  | "||"    { PIPEPIPE   }
  | "="     { EQ         }
  | "==" (blank* (size as w) (signletter as g))? { EQEQ (mk_swsize g w) }
  | "!=" (blank* (size as w) (signletter as g))? { BANGEQ (mk_swsize g w) }

  | _ as c  { invalid_char (L.of_lexbuf lexbuf) c }
  | eof     { EOF }

(* -------------------------------------------------------------------- *)
and comment lvl = parse
  | "*/"             { if lvl <= 0 then () else comment (lvl-1) lexbuf }
  | "/*"             { comment (lvl+1) lexbuf }
  | newline          { Lexing.new_line lexbuf; comment lvl lexbuf }
  | [^'\n']          { comment lvl lexbuf }
  | eof              { unterminated_comment (L.of_lexbuf lexbuf) }
