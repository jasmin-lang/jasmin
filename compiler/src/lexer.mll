{
  open Utils
  open Parser

  module L = Location

  let unterminated_comment loc =
    raise (Syntax.ParseError (loc, Some "unterminated comment"))

  let invalid_char loc (c : char) =
    let msg = Printf.sprintf "invalid char: `%c'" c in
    raise (Syntax.ParseError (loc, Some msg))

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
    "if"    , IF     ;
    "inline", INLINE ;
    "param" , PARAM  ;
    "reg"   , REG    ;
    "return", RETURN ;
    "stack" , STACK  ;
    "to"    , TO     ;
    "true"  , TRUE   ;
    "while" , WHILE  ;
  ]

  let keywords = Hash.of_enum (List.enum _keywords)
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

  | "["     { LBRACKET   }
  | "]"     { RBRACKET   }
  | "{"     { LBRACE     }
  | "}"     { RBRACE     }
  | "("     { LPAREN     }
  | ")"     { RPAREN     }
  | "_"     { UNDERSCORE }
  | "->"    { RARROW     }
  | ","     { COMMA      }
  | ";"     { SEMICOLON  }
  | "<="    { LE         }
  | "<"     { LT         }
  | ">="    { GE         }
  | ">"     { GT         }
  | "!"     { BANG       }
  | "+"     { PLUS       }
  | "-"     { MINUS      }
  | "*"     { STAR       }
  | "|"     { PIPE       }
  | "&"     { AMP        }
  | "^"     { HAT        }
  | "&&"    { AMPAMP     }
  | "||"    { PIPEPIPE   }
  | ">>"    { GTGT       }
  | "<<"    { LTLT       }
  | "="     { EQ         }
  | "=="    { EQEQ       }
  | "!="    { BANGEQ     }
  | "+="    { PLUSEQ     }
  | "-="    { MINUSEQ    }
  | "*="    { STAREQ     }
  | "|="    { PIPEEQ     }
  | "&="    { AMPEQ      }
  | "^="    { HATEQ      }
  | "^="    { HATEQ      }
  | ">>="   { GTGTEQ     }
  | "<<="   { LTLTEQ     }

  | _ as c  { invalid_char (L.of_lexbuf lexbuf) c }
  | eof     { EOF }

(* -------------------------------------------------------------------- *)
and comment lvl = parse
  | "*/"             { if lvl <= 0 then () else comment (lvl-1) lexbuf }
  | "/*"             { comment (lvl+1) lexbuf }
  | newline          { Lexing.new_line lexbuf; comment lvl lexbuf }
  | [^'\n']          { comment lvl lexbuf }
  | eof              { unterminated_comment (L.of_lexbuf lexbuf) }
