%{

open Asm_X64

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

%token RAX_ RBX_ RCX_ RDX_ RDI_ RSI_ RBP_ RSP_
%token R8_ R9_ R10_ R11_ R12_ R13_ R14_ R15_

%token COMMA DOLLAR

%token <Util.u64>  NAT

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
| c = CMOV { CMov c }

%inline unop:
| MUL  { Mul }

%inline triop:
| IMUL { IMul }

src:
| n=NAT LPAREN r=reg RPAREN { Smem(r,n) }
| r=reg                     { Sreg(r) }
| DOLLAR n=NAT              { Simm(n) }

dest:
| n=NAT LPAREN r=reg RPAREN { Dmem(r,n) }
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
