(* ** License
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

(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import Setoid Morphisms.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import ZArith.

Require Import strings word utils type var expr.
Require Import memory sem linear compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

(* TODO: int8 etc. have been replaced with word/nat, compiler may crash *)

Definition port_number := nat.
Definition interrupt_type := nat.
Definition selector := nat.

Inductive register : Set := EAX | ECX | EDX | EBX | ESP | EBP | ESI | EDI.
Inductive scale : Set := Scale1 | Scale2 | Scale4 | Scale8.
Inductive segment_register : Set := ES | CS | SS | DS | FS | GS.
Inductive control_register : Set := CR0 | CR2 | CR3 | CR4.
Inductive debug_register   : Set := DR0 | DR1 | DR2 | DR3 | DR6 | DR7.
Inductive rflag : Set := CF | PF | AF | ZF | SF | OF.

Definition rflag_of_string (s: string) :=
  match s with
  | "CF"%string => Some CF
  | "PF"%string => Some PF
  | "AF"%string => Some AF
  | "ZF"%string => Some ZF
  | "SF"%string => Some SF
  | "OF"%string => Some OF
  | _ => None
  end.

Record address : Set := mkAddress {
  addrDisp : word ; 
  addrBase : option register ; 
  addrIndex : option (scale * register)
}.

Inductive operand : Set := 
| Imm_op : word -> operand
| Reg_op : register -> operand
| Address_op : address -> operand
| Offset_op : word -> operand.

Inductive reg_or_immed : Set := 
| Reg_ri : register -> reg_or_immed
| Imm_ri : nat -> reg_or_immed.

Inductive condition_type : Set :=
| O_ct (* overflow *)
| NO_ct (* not overflow *)
| B_ct (* below, not above or equal *)
| NB_ct (* not below, above or equal *)
| E_ct (* equal, zero *)
| NE_ct (* not equal, not zero *)
| BE_ct (* below or equal, not above *)
| NBE_ct (* not below or equal, above *)
| S_ct (* sign *)
| NS_ct (* not sign *)
| P_ct (* parity, parity even *)
| NP_ct (* not parity, parity odd *)
| L_ct  (* less than, not greater than or equal to *)
| NL_ct (* not less than, greater than or equal to *)
| LE_ct (* less than or equal to, not greater than *)
| NLE_ct (* not less than or equal to, greater than *).

(* Floating point instruction syntax *)

Inductive fp_debug_register : Set := eMF | eDB | eBP | eUD | eNM | eDF | eSS | eGP | ePF | eAC | eMC.

Inductive fp_operand : Set := 
| FPS_op : nat -> fp_operand 	    (*an index from 0 to 7 relative to stack top *)
| FPM16_op : address -> fp_operand
| FPM32_op : address -> fp_operand
| FPM64_op : address -> fp_operand
| FPM80_op : address -> fp_operand. 

(* floating-point condition tpe *)
Inductive fp_condition_type : Set :=
| B_fct (* below *)
| E_fct (* equal *)
| BE_fct (* below or equal *)
| U_fct (* unordered *)
| NB_fct (* not below *)
| NE_fct (* not equal *)
| NBE_fct (* not below or equal *)
| NU_fct (* not unordered *).

(*MMX syntax *)

(* Eight 64-bit mmx registers; mmx registers are syntactically
   different from fpu registers, but are semantically mapped
   to the same set of eight 80-bit registers as FPU registers *)
Definition mmx_register := nat.

Inductive mmx_granularity : Set :=
| MMX_8                         (* 8 bits *)
| MMX_16                        (* 16 bits *)
| MMX_32                        (* 32 bits *)
| MMX_64.                       (* 64 bits *)

Inductive mmx_operand : Set := 
| GP_Reg_op : register -> mmx_operand
| MMX_Addr_op : address -> mmx_operand
| MMX_Reg_op : mmx_register -> mmx_operand
| MMX_Imm_op : word -> mmx_operand.

(*SSE syntax *)
(* 8 128-bit registers (XMM0 - XMM7) introduced, along with MXCSR word for status and control of these registers *)
Definition sse_register := nat.

(*mmreg means mmx register. *)
Inductive mxcsr: Set := FZ | Rpos | Rneg | RZ | RN | PM | UM | OM | ZM | DM | IM | DAZ | PE | UE |
			 OE | ZE | DE | IE.

Inductive sse_operand : Set := 
| SSE_XMM_Reg_op : sse_register -> sse_operand
| SSE_MM_Reg_op : mmx_register -> sse_operand 
| SSE_Addr_op : address -> sse_operand
| SSE_GP_Reg_op : register -> sse_operand (*r32 in manual*)
| SSE_Imm_op : word -> sse_operand.

(* The list of all instructions *)

Inductive instr : Set :=
(* "High-level" assembly-specific instructions *)
| LABEL : label -> instr

(* two parts:  1-byte opcode instructions, followed by 2-byte in alphabetical order,
   following Table B-13 *) 
| AAA 
| AAD 
| AAM 
| AAS 
(* w is the width bit; 
   with no operand override prefix, 
     when w is true, then it's a 32-bit operation;
     when w is false, then it's a 8-bit operation;
   with an operand override prefix,
     when w is true, it's a 16-bit operation;
     when w is false, it's a 8-bit operation;
   See load_op/set-op in X86Semantics.v *)
| ADC   : forall (w:bool)(op1 op2:operand), instr
| ADD   : forall (w:bool)(op1 op2:operand), instr
| AND   : forall (w:bool)(op1 op2:operand), instr
| ARPL  : forall (op1 op2:operand), instr
| BOUND : forall (op1 op2:operand), instr
| BSF   : forall (op1 op2:operand), instr
| BSR   : forall (op1 op2:operand), instr
| BSWAP : forall (r:register), instr
| BT    : forall (op1 op2:operand), instr
| BTC   : forall (op1 op2:operand), instr
| BTR   : forall (op1 op2:operand), instr
| BTS   : forall (op1 op2:operand), instr
| CALL  : forall (near:bool)(absolute: bool)(op1:operand)(sel:option selector), instr
| CDQ 
| CLC 
| CLD 
| CLI 
| CLTS 
| CMC
| CMOVcc : forall (ct:condition_type)(op1 op2: operand), instr
| CMP    : forall (w:bool)(op1 op2:operand), instr
| CMPS   : forall (w:bool), instr
| CMPXCHG: forall (w:bool)(op1 op2:operand), instr
| CPUID 
| CWDE 
| DAA 
| DAS
| DEC   : forall (w:bool)(op1:operand), instr
| DIV   : forall (w:bool)(op1:operand), instr

(*Floating-point syntax defined starting here. Table B-38 explains how to read instructions and B-39 has the
actual instruction details. Instructions can be found here: 
http://download.intel.com/products/processor/manual/325383.pdf*)
| F2XM1 : instr
| FABS : instr
(* zerod is true iff st(0) is the destination; 
   op1 is the destination when zerod=false *)
| FADD : forall (zerod: bool) (op1: fp_operand), instr
| FADDP : forall (op1: fp_operand), instr
| FBLD : forall (op1: fp_operand), instr
| FBSTP : forall (op1: fp_operand), instr
| FCHS : instr
(* FCLEX is the same as FWAIT followed FNCLEX
   | FCLEX : instr *)
| FCMOVcc : forall (ct:fp_condition_type)(op1: fp_operand), instr
| FCOM : forall (op1: fp_operand), instr
| FCOMP : forall (op1: fp_operand), instr
| FCOMPP : instr
| FCOMIP : forall (op1: fp_operand), instr
| FCOS : instr
| FDECSTP : instr
| FDIV : forall (zerod: bool) (op: fp_operand), instr
| FDIVP : forall (op1: fp_operand), instr
| FDIVR : forall (zerod: bool) (op: fp_operand), instr
| FDIVRP : forall (op1: fp_operand), instr
| FFREE : forall (op1: fp_operand), instr
| FIADD : forall (op1: fp_operand), instr
| FICOM : forall (op1: fp_operand), instr
| FICOMP : forall (op1: fp_operand), instr
| FIDIV : forall (op1: fp_operand), instr
| FIDIVR : forall (op1: fp_operand), instr
| FILD : forall (op1: fp_operand), instr
| FIMUL : forall (op1: fp_operand), instr
| FINCSTP : instr
(* FINIT is FWAIT followed by FNINIT;
   | FINIT : instr *)
| FIST : forall (op1: fp_operand), instr
| FISTP : forall (op1: fp_operand), instr
| FISUB : forall (op1: fp_operand), instr
| FISUBR : forall (op1: fp_operand), instr
| FLD : forall (op1: fp_operand), instr
| FLD1 : instr
| FLDCW : forall (op1: fp_operand), instr
| FLDENV : forall (op1: fp_operand), instr
| FLDL2E : instr
| FLDL2T : instr
| FLDLG2 : instr
| FLDLN2 : instr
| FLDPI : instr
| FLDZ : instr
| FMUL : forall (zerod: bool) (op1: fp_operand), instr
| FMULP : forall (op1: fp_operand), instr
| FNCLEX : instr
| FNINIT : instr
| FNOP : instr
| FNSAVE : forall (op1: fp_operand), instr
| FNSTCW : forall (op1 : fp_operand), instr
(* FNSTSW None means that storing the status word to AX *)
| FNSTSW : forall (op1 : option fp_operand), instr
| FPATAN : instr
| FPREM : instr
| FPREM1 : instr
| FPTAN : instr
| FRNDINT : instr
| FRSTOR : forall (op1: fp_operand), instr
(* FSAVE's encoding the same as FWAIT followed FNSAVE
   | FSAVE : forall (op1: fp_operand), instr *)
| FSCALE : instr
| FSIN : instr
| FSINCOS : instr
| FSQRT : instr
| FST : forall (op1: fp_operand), instr

(* FSTCW's is the same as FWAIT followed by FNSTCW
   | FSTCW : forall (op1: fp_operand), instr *)

| FSTENV : forall (op1: fp_operand), instr
| FSTP : forall (op1: fp_operand), instr

(* FSTSW is the same as FWAIT followed by FNSTSW 
   | FSTSW : forall (op1: option fp_operand), instr *)

(* st(0) <- st(0) - op, when zerod is true;
   op <- op - st(0), when zerod is false and op can only be st(i) *)
| FSUB : forall (zerod: bool) (op: fp_operand), instr
| FSUBP : forall (op1: fp_operand), instr
(* reverse subtraction
   st(0) <- op - st(0), when zerod is true;
   op <- st(0) - op, when zerod is false and op can only be st(i) *)
| FSUBR : forall (zerod: bool) (op: fp_operand), instr
| FSUBRP : forall (op1: fp_operand), instr
| FTST : instr
| FUCOM : forall (op1: fp_operand), instr
| FUCOMP : forall (op1: fp_operand), instr
| FUCOMPP : instr
| FUCOMI : forall (op1: fp_operand), instr
| FUCOMIP : forall (op1: fp_operand), instr
| FXAM : instr
| FXCH : forall (op1: fp_operand), instr
| FXTRACT : instr
| FYL2X : instr
| FYL2XP1 : instr
| FWAIT : instr
(*Floating-Point syntax ends here for now*)
(*MMX syntax starting here (from table B.5.3) *)
| EMMS : instr
| MOVD : forall (op1 op2: mmx_operand), instr
| MOVQ : forall (op1 op2: mmx_operand), instr
| PACKSSDW : forall (op1 op2: mmx_operand), instr
| PACKSSWB : forall (op1 op2: mmx_operand), instr
| PACKUSWB : forall (op1 op2: mmx_operand), instr
| PADD : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PADDS : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PADDUS : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PAND : forall  (op1 op2 : mmx_operand), instr
| PANDN : forall  (op1 op2 : mmx_operand), instr
| PCMPEQ : forall  (gg:mmx_granularity) (op1 op2 : mmx_operand), instr
| PCMPGT : forall  (gg:mmx_granularity) (op1 op2 : mmx_operand), instr
| PMADDWD : forall  (op1 op2 : mmx_operand), instr
| PMULHUW : forall  (op1 op2 : mmx_operand), instr
| PMULHW : forall  (op1 op2 : mmx_operand), instr
| PMULLW : forall  (op1 op2 : mmx_operand), instr
| POR : forall  (op1 op2 : mmx_operand), instr
| PSLL : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PSRA : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PSRL : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PSUB : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PSUBS : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PSUBUS : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PUNPCKH : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PUNPCKL : forall (gg:mmx_granularity) (op1 op2: mmx_operand), instr
| PXOR : forall  (op1 op2 : mmx_operand), instr
(*End of MMX syntax *)

(*SSE Syntax (Table B.8 in manual) *)
| ADDPS : forall (op1 op2: sse_operand), instr
| ADDSS : forall (op1 op2: sse_operand), instr
| ANDNPS : forall (op1 op2: sse_operand), instr
| ANDPS : forall (op1 op2: sse_operand), instr
| CMPPS : forall (op1 op2:sse_operand) (imm:nat), instr
| CMPSS : forall (op1 op2: sse_operand) (imm:nat), instr
| COMISS : forall (op1 op2: sse_operand), instr
| CVTPI2PS : forall (op1 op2: sse_operand), instr
| CVTPS2PI : forall (op1 op2: sse_operand), instr
| CVTSI2SS : forall (op1 op2: sse_operand), instr
| CVTSS2SI : forall (op1 op2: sse_operand), instr
| CVTTPS2PI : forall (op1 op2: sse_operand), instr
| CVTTSS2SI : forall (op1 op2: sse_operand), instr
| DIVPS : forall (op1 op2: sse_operand), instr
| DIVSS : forall (op1 op2: sse_operand), instr
| LDMXCSR : forall (op1: sse_operand), instr
| MAXPS : forall (op1 op2: sse_operand), instr 
| MAXSS : forall (op1 op2: sse_operand), instr
| MINPS : forall (op1 op2: sse_operand), instr
| MINSS : forall (op1 op2: sse_operand), instr
| MOVAPS : forall (op1 op2: sse_operand), instr
| MOVHLPS : forall (op1 op2: sse_operand), instr
| MOVHPS : forall (op1 op2: sse_operand), instr
| MOVLHPS : forall (op1 op2: sse_operand), instr
| MOVLPS : forall (op1 op2: sse_operand), instr
| MOVMSKPS : forall (op1 op2: sse_operand), instr
| MOVSS : forall (op1 op2: sse_operand), instr
| MOVUPS : forall (op1 op2: sse_operand), instr
| MULPS : forall (op1 op2: sse_operand), instr
| MULSS : forall (op1 op2: sse_operand), instr
| ORPS : forall (op1 op2: sse_operand), instr
| RCPPS : forall (op1 op2: sse_operand), instr
| RCPSS : forall (op1 op2: sse_operand), instr
| RSQRTPS : forall (op1 op2: sse_operand), instr
| RSQRTSS : forall (op1 op2: sse_operand), instr
| SHUFPS : forall (op1 op2: sse_operand) (imm:nat), instr
| SQRTPS : forall (op1 op2: sse_operand), instr
| SQRTSS : forall (op1 op2: sse_operand), instr
| STMXCSR : forall (op1 : sse_operand), instr
| SUBPS : forall (op1 op2: sse_operand), instr
| SUBSS : forall (op1 op2: sse_operand), instr
| UCOMISS : forall (op1 op2: sse_operand), instr
| UNPCKHPS : forall (op1 op2: sse_operand), instr
| UNPCKLPS : forall (op1 op2: sse_operand), instr
| XORPS : forall (op1 op2: sse_operand), instr
| PAVGB : forall (op1 op2: sse_operand), instr
| PEXTRW : forall (op1 op2: sse_operand) (imm:nat), instr
| PINSRW : forall (op1 op2: sse_operand) (imm:nat), instr
| PMAXSW : forall (op1 op2: sse_operand), instr
| PMAXUB : forall (op1 op2: sse_operand), instr
| PMINSW : forall (op1 op2: sse_operand), instr
| PMINUB : forall (op1 op2: sse_operand), instr
| PMOVMSKB : forall (op1 op2: sse_operand), instr
(*| PMULHUW : forall (op1 op2: sse_operand), instr *)
| PSADBW : forall (op1 op2: sse_operand), instr
| PSHUFW : forall (op1 op2: sse_operand) (imm:nat), instr
| MASKMOVQ : forall (op1 op2: sse_operand), instr
| MOVNTPS : forall (op1 op2: sse_operand), instr
| MOVNTQ : forall (op1 op2: sse_operand), instr
| PREFETCHT0 : forall (op1: sse_operand), instr
| PREFETCHT1 : forall (op1: sse_operand), instr
| PREFETCHT2 : forall (op1: sse_operand), instr
| PREFETCHNTA : forall (op1: sse_operand), instr
| SFENCE: instr
(*end SSE, start SSE2 *)

(*End of SSE Syntax *)
| HLT  
| IDIV  : forall (w:bool)(op1:operand), instr
(* This one is kind of funny -- there are three cases:
   one operand, two operand, and three operand. The one operand
   form is precise and implicitly uses EAX; the other two variants
   can potentially lose some data due to overflow. *)
| IMUL  : forall (w:bool)(op1:operand) (opopt: option operand) (iopt:option nat), instr
| IN    : forall (w:bool)(p: option port_number), instr
| INC   : forall (w:bool)(op1:operand), instr
| INS   : forall (w:bool), instr
| INTn  : forall (it:interrupt_type),instr
| INT   : instr
| INTO  : instr
| INVD  : instr
| INVLPG : forall (op1:operand), instr
| IRET   : instr
| Jcc   : condition_type -> label -> instr
| JCXZ  : forall (b:word), instr
| JMP   : label -> instr
| LAHF
| LAR   : forall (op1 op2:operand), instr
| LDS   : forall (op1 op2:operand), instr
| LEA   : forall (op1 op2:operand), instr
| LEAVE
| LES   : forall (op1 op2:operand), instr
| LFS   : forall (op1 op2:operand), instr
| LGDT  : forall (op1:operand), instr
| LGS   : forall (op1 op2:operand), instr
| LIDT  : forall (op1:operand), instr
| LLDT  : forall (op1:operand), instr
| LMSW  : forall (op1:operand), instr
| LODS  : forall (w:bool), instr
| LOOP  : forall (disp:nat), instr
| LOOPZ : forall (disp:nat), instr
| LOOPNZ: forall (disp:nat), instr
| LSL   : forall (op1 op2:operand), instr
| LSS   : forall (op1 op2:operand), instr
| LTR   : forall (op1:operand), instr
| MOV   : forall (w:bool)(op1 op2:operand), instr
(* Note:  when direction is true, we move the first operand to the second.  
 * When the direction is false, we move the second operand to the first. *)
| MOVCR : forall (direction:bool)(cr:control_register)(r:register), instr
| MOVDR : forall (direction:bool)(dr:debug_register)(r:register), instr
| MOVSR : forall (direction:bool)(sr:segment_register)(op1:operand), instr
| MOVBE : forall (op1 op2:operand), instr
| MOVS  : forall (w:bool), instr
| MOVSX : forall (w:bool)(op1 op2:operand), instr
| MOVZX : forall (w:bool)(op1 op2:operand), instr
| MUL   : forall (w:bool)(op1:operand), instr
| NEG   : forall (w:bool)(op:operand), instr
| NOP   : forall (op:operand), instr
| NOT   : forall (w:bool)(op:operand), instr
| OR    : forall (w:bool)(op1 op2:operand), instr
| OUT   : forall (w:bool)(p:option port_number), instr
| OUTS  : forall (w:bool), instr
| POP   : forall (op1:operand), instr
| POPSR : forall (sr:segment_register), instr
| POPA 
| POPF
| PUSH  : forall (w:bool)(op1:operand), instr
| PUSHSR: forall (sr:segment_register), instr
| PUSHA
| PUSHF
| RCL   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| RCR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| RDMSR     : instr
| RDPMC     : instr
| RDTSC     : instr
| RDTSCP    : instr
| RET   : instr
| ROL   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| ROR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| RSM
| SAHF
| SAR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| SBB   : forall (w:bool)(op1 op2:operand), instr
| SCAS  : forall (w:bool), instr
| SETcc : forall (ct:condition_type)(op1:operand), instr
| SGDT  : forall (op1:operand), instr
| SHL   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| SHLD  : forall (op1:operand)(r:register)(ri:reg_or_immed), instr
| SHR   : forall (w:bool)(op1:operand)(ri:reg_or_immed), instr
| SHRD  : forall (op1:operand)(r:register)(ri:reg_or_immed), instr
| SIDT  : forall (op1:operand), instr
| SLDT  : forall (op1:operand), instr
| SMSW  : forall (op1:operand), instr
| STC
| STD
| STI
| STOS  : forall (w:bool), instr
| STR   : forall (op1:operand), instr
| SUB   : forall (w:bool)(op1 op2:operand), instr
| TEST  : forall (w:bool)(op1 op2:operand), instr
| UD2
| VERR  : forall (op1:operand), instr
| VERW  : forall (op1:operand), instr
(* | WAIT  removed because it's the same as FWAIT*)
| WBINVD
| WRMSR
| XADD  : forall (w:bool)(op1 op2:operand), instr
| XCHG  : forall (w:bool)(op1 op2:operand), instr
| XLAT 
| XOR   : forall (w:bool)(op1 op2:operand), instr.

Definition cmd := seq instr.

Definition rflag_of_var_i (v: var_i) :=
  match v with
  | VarI (Var sbool s) _ => rflag_of_string s
  | _ => None
  end.

Definition assemble_cond ii (e: pexpr) :=
  match e with
  | Pvar v =>
    match (rflag_of_var_i v) with
    | Some CF => ciok B_ct
    | Some PF => ciok P_ct
    | Some ZF => ciok E_ct
    | Some SF => ciok S_ct
    | Some OF => ciok O_ct
    | _ => cierror ii (Cerr_assembler "branching variable is not a valid rflag")
    end
  | Pnot (Pvar v) =>
    match (rflag_of_var_i v) with
    | Some CF => ciok NB_ct
    | Some PF => ciok NP_ct
    | Some ZF => ciok NE_ct
    | Some SF => ciok NS_ct
    | Some OF => ciok NO_ct
    | _ => cierror ii (Cerr_assembler "branching variable is not a valid rflag")
    end
  | _ => cierror ii (Cerr_assembler "invalid branching")
  end.

Definition assemble_i (li: linstr) : ciexec instr :=
  let (ii, i) := li in
  match i with
  | Lassgn _ _ _ => cierror ii (Cerr_assembler "assgn")
  | Lopn l o p => cierror ii (Cerr_assembler "opn")
  | Llabel l => ciok (LABEL l)
  | Lgoto l => ciok (JMP l)
  | Lcond e l =>
     Let cond := assemble_cond ii e in
     ciok (Jcc cond l)
  | Lreturn => ciok RET
  end.

Definition assemble_c (lc: lcmd) : ciexec cmd :=
  mapM assemble_i lc.

Record afundef := AFundef {
 afd_stk_size : Z;
 afd_nstk : Ident.ident;
 afd_arg  : seq var_i;
 afd_body : cmd;
 afd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
}.

Definition aprog := seq (funname * afundef).

Definition assemble_fd (fd: lfundef) :=
  Let fd' := assemble_c (lfd_body fd) in
  ok (AFundef (lfd_stk_size fd) (lfd_nstk fd) (lfd_arg fd) fd' (lfd_res fd)).

Definition assemble_prog (p: lprog) : cfexec aprog :=
  map_cfprog assemble_fd p.
