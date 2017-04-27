(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 * Copyright 2017 Google Inc.
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

{
  open IL_MilParser

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

  | "u8"    { T_U8   }
  | "u16"   { T_U16  }
  | "u32"   { T_U32  }
  | "u64"   { T_U64  }
  | "u128"  { T_U128 }
  | "u256"  { T_U256 }
  | "bool"  { T_BOOL }
  | "int"   { T_INT  }

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

  | "reg"   { REG }
  | "stack" { STACK }
  | "inline" { INLINE }
  | "param"  { PARAM }
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
  | "inl!"             { INLEXCL  }
  | "decl!"            { DECL     }
  | "fn"               { FN       }
  | "return"           { RETURN   }

  | ('-'? ['0'-'9']+) as s { INT(s) }
  | ("0x" ['0'-'9' 'a'-'f' '_']+) as s { INT(s) }

  | (['a'-'z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* as s)
    '.' ((['0'-'9']+) as si)
    { NID(s,si) }

  | ['a'-'z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']* as s
    { NID(s,"") }

and comment = parse
  | "*/"        { () }
  | "/*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and line_comment = parse
  | newline { () }
  | _       { line_comment lexbuf }
