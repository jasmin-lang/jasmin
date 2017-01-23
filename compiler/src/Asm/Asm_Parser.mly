/*
(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
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
*/

%{

open Asm_X64
open Arith

%}

/*======================================================================*/
/* Tokens */

%token EOF

%token LPAREN RPAREN

%token MOV
%token MUL IMUL
%token ADD ADC
%token SUB SBB
%token <Asm_X64.cond> CMOV
%token SHR SHL
%token AND XOR

%token RAX_ RBX_ RCX_ RDX_ RDI_ RSI_ RBP_ RSP_
%token R8_ R9_ R10_ R11_ R12_ R13_ R14_ R15_

%token COMMA DOLLAR

%token <int64>  NAT

%type <Asm_X64.instr> instr
%type <Asm_X64.instr list> instrs

%start instr

%start instrs

%%

reg :
| RAX_ { RAX }
| RBX_ { RBX }
| RCX_ { RCX }
| RDX_ { RDX }
| RDI_ { RDI }
| RSI_ { RSI }
| RBP_ { RBP }
| RSP_ { RSP }
| R8_  { R8  }
| R9_  { R9  }
| R10_ { R10 }
| R11_ { R11 }
| R12_ { R12 }
| R13_ { R13 }
| R14_ { R14 }
| R15_ { R15 }

%inline binop:
| MOV  { Mov }
| ADD  { Add }
| ADC  { Adc }
| SUB  { Sub }
| SBB  { Sbb }
| c = CMOV { Cmov c }
| SHR  { Shr }
| SHL  { Shl }
| AND  { And }
| XOR  { Xor }

%inline unop:
| MUL  { Mul }

%inline triop:
| IMUL { IMul }

src:
| n=NAT LPAREN r=reg RPAREN { Smem(r,U64.of_int64 n) }
| r=reg                     { Sreg(r) }
| DOLLAR n=NAT              { Simm(U64.of_int64 n) }

dest:
| n=NAT LPAREN r=reg RPAREN { Dmem(r,U64.of_int64 n) }
| r=reg                     { Dreg(r) }

instr:
| o=unop s=src
  { Unop(o,s) }
| o=triop s1=src COMMA s2=src COMMA d=dest
  { Triop(o,s1,s2,d) }
| o=binop s=src COMMA d=dest
  { Binop(o,s,d) }


instrs:
| is = instr* EOF { is }
