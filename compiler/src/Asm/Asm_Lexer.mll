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
  | "shr"    { SHR }
  | "shl"    { SHL }
  | "and"    { AND }
  | "xor"    { XOR }


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
