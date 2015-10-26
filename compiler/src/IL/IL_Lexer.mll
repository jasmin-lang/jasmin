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
  | eof     { EOF }

  | "["     { LBRACK }
  | "]"     { RBRACK }
  | "{"     { LCBRACE }
  | "}"     { RCBRACE }
  | "("     { LPAREN }
  | ")"     { RPAREN }


  | "="     { EQ }
  | "!="    { INEQ }
  | "+="    { PLUSEQ }
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

  | "-"     { MINUS }
  | "*"     { STAR }
  | "+"     { PLUS }
  | "&"     { BAND }
  | "&&"    { LAND }
  | ";"     { SEMICOLON }
  | "?"     { QUESTION }
  | "!"     { EXCL }
  | "true"  { TRUE }
  | "false" { FALSE }
  | ">>"    { SHR }
  | "<<"    { SHL }
  | "^"     { XOR }

  | "for"    { FOR }
  | "in"     { IN }
  | "if"     { IF }
  | "else"   { ELSE }
  | "else" blank+ "if" { ELIF }
  | "extern" { EXTERN }
  | "fn"     { FN }
  | "return" { RETURN }

  | ('-'? ['0'-'9']+) as s { INT(Int64.of_string s) }
  | ['a'-'z' 'A'-'Z' '_' '0'-'9']* as s
    { ID s }

and comment = parse
  | "*/"        { () }
  | "/*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
