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

  let unescape loc (s: string) =
    try Scanf.unescaped s with
    | Scanf.Scan_failure msg ->
      raise (Syntax.ParseError (loc, Some (Format.asprintf "ill-formed string (%s)" msg)))

  let _keywords = [
    "u8"    , T_U8   ;
    "u16"   , T_U16  ;
    "u32"   , T_U32  ;
    "u64"   , T_U64  ;
    "u128"  , T_U128 ;
    "u256"  , T_U256 ;

    "bool"  , T_BOOL ;
    "int"   , T_INT  ;
    
    "const" , CONSTANT; 
    "downto", DOWNTO ;
    "else"  , ELSE   ;
    "exec"  , EXEC   ;
    "false" , FALSE  ;
    "fn"    , FN     ;
    "for"   , FOR    ;
    "from"  , FROM   ;
    "global", GLOBAL ;
    "if"    , IF     ;
    "inline", INLINE ;
    "mut"   , MUTABLE;
    "namespace", NAMESPACE;
    "param" , PARAM  ;
    "ptr"   , POINTER;
    "reg"   , REG    ;
    "require", REQUIRE;
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

  let mk_sign : char option -> S.sign =
  function
  | Some c -> sign_of_char c
  | None   -> `Unsigned 

  let size_of_string =
  function
  | "8"   -> Wsize.U8
  | "16"  -> Wsize.U16
  | "32"  -> Wsize.U32
  | "64"  -> Wsize.U64
  | "128" -> Wsize.U128
  | "256" -> Wsize.U256
  | _ -> assert false

  let mksizesign sw s = size_of_string sw, sign_of_char s

  let mk_gensize = function
    | "1"   -> `W1 
    | "2"   -> `W2
    | "4"   -> `W4
    | "8"   -> `W8
    | "16"  -> `W16
    | "32"  -> `W32
    | "64"  -> `W64
    | "128" -> `W128
    | _     -> assert false


  let mk_vsize   = function
    | "2"  -> `V2  
    | "4"  -> `V4
    | "8"  -> `V8
    | "16" -> `V16 
    | "32" -> `V32
    | _    ->  assert false 
 
  let mkvsizesign r s g = mk_vsize r, sign_of_char s, mk_gensize g

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
let gensize = "1" | "2" | "4" | "8" | "16" | "32" | "64" | "128" 
let vsize   = "2" | "4" | "8" | "16" | "32" 


(* -------------------------------------------------------------------- *)
rule main = parse
  | newline { Lexing.new_line lexbuf; main lexbuf }
  | blank+  { main lexbuf }

  | "/*" { comment 0 lexbuf; main lexbuf }

  | "//" [^'\n']* newline { Lexing.new_line lexbuf; main lexbuf }
  | "//" [^'\n']* eof     { main lexbuf }

  | '"' (([^'"' '\\']|'\\' _)* as s) '"' { STRING (unescape (L.of_lexbuf lexbuf) s) }

  (* Why this is needed *)
  | ((*'-'?*) digit+) as s   
      { INT (Z.of_string s) } 

  | ('0' ['x' 'X'] hexdigit+) as s
      { INT (Z.of_string s) }

  | ident as s
      { Option.default (NID s) (Hash.find_option keywords s) }

  | (size as sw) (signletter as s)                { SWSIZE(mksizesign sw s)  }
  | (vsize as r) (signletter as s) (gensize as g) { SVSIZE(mkvsizesign r s g)}
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
  | "::"    { COLONCOLON  }

  | ">>r"                   { ROR              }
  | "<<r"                   { ROL              }
  | "<<"                    { LTLT            }
  | "<=" (signletter as s)? { LE   (mk_sign s) }
  | "<"  (signletter as s)? { LT   (mk_sign s) }
  | ">>" (signletter as s)? { GTGT (mk_sign s) }
  | ">=" (signletter as s)? { GE   (mk_sign s) }
  | ">"  (signletter as s)? { GT   (mk_sign s) }

  | "."  { DOT      }
  | "!"  { BANG     }
  | "+"  { PLUS     }
  | "-"  { MINUS    }
  | "*"  { STAR     }
  | "/"  { SLASH    }
  | "%"  { PERCENT  }
  | "|"  { PIPE     }
  | "&"  { AMP      }
  | "^"  { HAT      }
  | "&&" { AMPAMP   }
  | "||" { PIPEPIPE }
  | "="  { EQ       }
  | "==" { EQEQ     }
  | "!=" { BANGEQ   }
  | "#unaligned" { UNALIGNED   }
  | "#aligned" { ALIGNED   }

  | _ as c  { invalid_char (L.of_lexbuf lexbuf) c }
  | eof     { EOF }

(* -------------------------------------------------------------------- *)
and comment lvl = parse
  | "*/"             { if lvl <= 0 then () else comment (lvl-1) lexbuf }
  | "/*"             { comment (lvl+1) lexbuf }
  | newline          { Lexing.new_line lexbuf; comment lvl lexbuf }
  | [^'\n']          { comment lvl lexbuf }
  | eof              { unterminated_comment (L.of_lexbuf lexbuf) }
