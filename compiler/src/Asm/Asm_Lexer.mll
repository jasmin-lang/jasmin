{
  open Asm_Parser
  open Asm_X64

  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+  { lex lexbuf }
  | "#"     { comment lexbuf; lex lexbuf }
  | eof     { EOF }

  | "mov"    { MOV }
  | "movq"   { MOV }
  | "mul"    { MUL }
  | "mulq"   { MUL }
  | "imulq"  { IMUL }
  | "add"    { ADD }
  | "adc"    { ADC }
  | "sub"    { SUB }
  | "sbb"    { SBB }
  | "cmovb"  { CMOV(CfSet(true)) }
  | "cmovnb" { CMOV(CfSet(false)) }


  | "("      { LPAREN }
  | ")"      { RPAREN }

  | "%rax"   { RAX_ }
  | "%rbx"   { RBX_ }
  | "%rcx"   { RCX_ }
  | "%rdx"   { RDX_ }
  | "%rdi"   { RDI_ }
  | "%rsi"   { RSI_ }
  | "%rbp"   { RBP_ }
  | "%rsp"   { RSP_ }
  | "%r8"    { R8_  }
  | "%r9"    { R9_  }
  | "%r10"   { R10_ }
  | "%r11"   { R11_ }
  | "%r12"   { R12_ }
  | "%r13"   { R13_ }
  | "%r14"   { R14_ }
  | "%r15"   { R15_ }

  | ","     { COMMA }
  | "$"     { DOLLAR }

  | ['0'-'9']['0'-'9']* as s { NAT(Int64.of_string(s)) }

and comment = parse
  | newline     { () }
  | eof         { () }
  | _           { comment lexbuf }
