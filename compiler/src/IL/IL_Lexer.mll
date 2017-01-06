{
  open IL_Parser

  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+  { lex lexbuf }
  | "/*"    { comment lexbuf; lex lexbuf }
  | "//"    { line_comment lexbuf; lex lexbuf }
  | eof     { EOF }

  | "["     { LBRACK }
  | "]"     { RBRACK }
  | "{"     { LCBRACE }
  | "}"     { RCBRACE }
  | "("     { LPAREN }
  | ")"     { RPAREN }

  | "->"    { LARROW }

  | ":"     { COLON }

  | "b8"    { T_U8   }
  | "b16"   { T_U16  }
  | "b32"   { T_U32  }
  | "b64"   { T_U64  }
  | "b128"  { T_U128 }
  | "b256"  { T_U256 }
  | "b1"    { T_BOOL }
  | "uint"  { T_INT  }

  | "_"     { UNDERSCORE }

  | "="     { EQ }
  | "=="    { EQEQ }
  | "!="    { INEQ }
  | "+="    { PLUSEQ }
  | "*="    { MULEQ }
  | "-="    { MINUSEQ }
  | "&="    { BANDEQ }
  | "<="    { LEQ }
  | "<"     { LESS }
  | ">="    { GEQ }
  | ">"     { GREATER }
  | ".."    { DOTDOT }
  | ","     { COMMA }
  | ">>="   { SHREQ }
  | "<<="   { SHLEQ }
  | "^="    { XOREQ }
  | "|="    { OREQ }

  | "-"     { MINUS }
  | "*"     { STAR }
  | "+"     { PLUS }
  | "&"     { BAND }
  | "&&"    { LAND }
  | "||"    { LOR }
  | ";"     { SEMICOLON }
  | "!"     { EXCL }
  | "true"  { TRUE }
  | "false" { FALSE }
  | ">>"    { SHR }
  | "<<"    { SHL }
  | "^"     { XOR }
  | "|"     { OR }
  | "$"     { DOLLAR }

  | "reg!"   { REG }
  | "stack!" { STACK }
  | "inline!" { INLINE }
  | "const"  { CONST }
  | "MEM"    { MEM }

  | "for"              { FOR      }
  | "when"             { WHEN     }
  | "while"            { WHILE    }
  | "do"               { DO       }
  | "in"               { IN       }
  | "if"               { IF       }
  | "else"             { ELSE     }
  | "else" blank+ "if" { ELIF     }
  | "pub"              { PUB      }
  | "mut"              { MUT      }
  | "jc!"              { JCEXCL   }
  | "var!"             { VAREXCL  }
  | "decl!"            { DECL     }
  | "code!"            { CODEEXCL }
  | "fn"               { FN       }
  | "return"           { RETURN   }

  | ('-'? ['0'-'9']+) as s { INT(s) }
  | ("0x" ['0'-'9' 'a'-'f' '_']+) as s { INT(s) }

  | (['a'-'z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* as s)
    '.' ((['0'-'9']+) as si)
    { NID(s,si) }

  | ['a'-'z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* as s
    { NID(s,"") }

  | "#![" (['a'-'z' '_' 'A'-'Z' '_' '0'-'9' ')' '(']+ as s) "]"
    { RUST_ATTRIBUTE(s) }

  | "rust!" blank* "{"
    { RUST_SECTION (rust_sec (Buffer.create 100) 0 lexbuf) }

  | "#[macro_use]" blank+ "extern" blank+ "crate" blank+ "jasmin" blank* ";"
    { EXTERN_JASMIN }

and rust_sec buf opened = parse
  | "}"   { if opened=0 then (
              Buffer.contents buf
            ) else (
              Buffer.add_char buf '}';
              rust_sec buf (opened - 1) lexbuf
            ) }
  | "{"   { Buffer.add_char buf '{'; rust_sec buf (opened + 1) lexbuf }
  | _     { Buffer.add_string buf (Lexing.lexeme lexbuf); rust_sec buf opened lexbuf }
  | "/*"  { comment lexbuf; rust_sec buf opened lexbuf }
  | "//"  { line_comment lexbuf; rust_sec buf opened lexbuf }
  | eof   { raise (Error "end-of-file inside rust! { .. }") }

and comment = parse
  | "*/"        { () }
  | "/*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and line_comment = parse
  | newline { () }
  | _       { line_comment lexbuf }