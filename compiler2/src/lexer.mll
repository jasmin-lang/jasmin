{
  open Utils
  open Parser

  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")

  let invalid_char (c : char) =
    raise (Error (Printf.sprintf "invalid char: `%c'" c))

  let _keywords = [
    "u8"    , T_U8   ;
    "u16"   , T_U16  ;
    "u32"   , T_U32  ;
    "u64"   , T_U64  ;
    "u128"  , T_U128 ;
    "u256"  , T_U256 ;
    "bool"  , T_BOOL ;
    "int"   , T_INT  ;
    "reg"   , REG    ;
    "stack" , STACK  ;
    "inline", INLINE ;
    "param" , PARAM  ;
    "MEM"   , MEM    ;
    "true"  , TRUE   ;
    "false" , FALSE  ;
    "for"   , FOR    ;
    "when"  , WHEN   ;
    "while" , WHILE  ;
    "do"    , DO     ;
    "in"    , IN     ;
    "if"    , IF     ;
    "else"  , ELSE   ;
    "pub"   , PUB    ;
    "mut"   , MUT    ;
    "fn"    , FN     ;
    "return", RETURN ;
  ]

  let keywords = Hash.of_enum (List.enum _keywords)
}

(* -------------------------------------------------------------------- *)
let blank    = [' ' '\t' '\r' '\n']
let newline  = '\n'
let digit    = ['0'-'9']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']
let lower    = ['a'-'z']
let upper    = ['A'-'Z']
let letter   = (lower | upper)
let idletter = letter | '_'
let ident    = idletter (idletter | digit)*

(* -------------------------------------------------------------------- *)
rule main = parse
  | blank+  { main lexbuf }

  | "/*" { comment 0 lexbuf; main lexbuf }
  | "//" _* (newline | eof) { main lexbuf }

  | ('-'? digit+) as s
      { INT (Bigint.of_string s) }

  | ("0x" hexdigit+) as s
      { INT (Bigint.of_string s) }

  | ident+ as s
      { odfl (NID s) (Hash.find_option keywords s) }

  | "["     { LBRACK     }
  | "]"     { RBRACK     }
  | "{"     { LCBRACE    }
  | "}"     { RCBRACE    }
  | "("     { LPAREN     }
  | ")"     { RPAREN     }
  | "->"    { LARROW     }
  | ":"     { COLON      }
  | "_"     { UNDERSCORE }
  | "="     { EQ         }
  | "=="    { EQEQ       }
  | "!="    { INEQ       }
  | "+="    { PLUSEQ     }
  | "*="    { MULEQ      }
  | "-="    { MINUSEQ    }
  | "&="    { BANDEQ     }
  | "<="    { LEQ        }
  | "<"     { LESS       }
  | ">="    { GEQ        }
  | ">"     { GREATER    }
  | ".."    { DOTDOT     }
  | ","     { COMMA      }
  | ">>="   { SHREQ      }
  | "<<="   { SHLEQ      }
  | "^="    { XOREQ      }
  | "|="    { OREQ       }
  | "-"     { MINUS      }
  | "*"     { STAR       }
  | "+"     { PLUS       }
  | "&"     { BAND       }
  | "&&"    { LAND       }
  | "||"    { LOR        }
  | ";"     { SEMICOLON  }
  | "!"     { EXCL       }
  | ">>"    { SHR        }
  | "<<"    { SHL        }
  | "^"     { XOR        }
  | "|"     { OR         }
  | "$"     { DOLLAR     }

  | _ as c  { invalid_char c }
  | eof     { EOF }

(* -------------------------------------------------------------------- *)
and comment lvl = parse
  | "*/"        { if lvl <= 0 then () else comment (lvl-1) lexbuf }
  | "/*"        { comment (lvl+1) lexbuf }
  | _+          { comment lvl lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lvl lexbuf }
  | eof         { unterminated_comment () }
