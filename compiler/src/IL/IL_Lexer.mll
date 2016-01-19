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

  | "u64"   { T_U64 }
  | "bool"  { T_BOOL }

  | "="     { EQ }
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
  | "|="    { OREQ  }

  | "-"     { MINUS }
  | "*"     { STAR }
  | "+"     { PLUS }
  | "&"     { BAND }
  | "&&"    { LAND }
  | ";"     { SEMICOLON }
  | "!"     { EXCL }
  | "true"  { TRUE }
  | "false" { FALSE }
  | ">>"    { SHR }
  | "<<"    { SHL }
  | "^"     { XOR }
  | "|"     { OR }
  | "$"     { DOLLAR }

  | "reg"    { REG }
  | "stack"  { STACK }
  | "inline" { INLINE }
  | "flag"   { FLAG }
  | "param"  { PARAM }
  | "MEM"    { MEM }

  | "for"    { FOR }
  | "for:"   { FORCOLON }
  | "in"     { IN }
  | "if"     { IF }
  | "else"   { ELSE }
  | "else" blank+ "if" { ELIF }
  | "extern" { EXTERN }
  | "fn"     { FN }
  | "python" { PYTHON }
  | "return" { RETURN }

  | ('-'? ['0'-'9']+) as s { INT(s) }
  | ("0x" ['0'-'9' 'a'-'f' '_']+) as s { INT(s) }

  | ['a'-'z']['a'-'z' 'A'-'Z' '_' '0'-'9']* as s
    { ID s }

and comment = parse
  | "*/"        { () }
  | "/*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and line_comment = parse
  | newline { () }
  | _       { line_comment lexbuf }