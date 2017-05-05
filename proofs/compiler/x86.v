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

(* * Syntax and semantics of the x86_64 target language *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect.
Require Import expr linear compiler_util low_memory.

Import Ascii.
Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Definition selector := nat.

Variant register : Set :=
    RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

Scheme Equality for register.
Definition register_eqP : Equality.axiom register_eq_dec.
Proof.
  move=> x y.
  case: register_eq_dec=> H; [exact: ReflectT|exact: ReflectF].
Qed.

Definition register_eqMixin := EqMixin register_eqP.
Canonical  register_eqType := EqType register register_eqMixin.

Definition string_of_register (r: register) : string :=
  match r with
  | RAX => "RAX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RBX => "RBX"
  | RSP => "RSP"
  | RBP => "RBP"
  | RSI => "RSI"
  | RDI => "RDI"
  | R8 => "R8"
  | R9 => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  end%string.

Definition reg_of_string (s: string) : option register :=
  match s with
  | String c0 tl =>
    if ascii_dec c0 "R" then
    match tl with
    | String c1 tl =>
      match tl with
      | EmptyString =>
        if ascii_dec c1 "8" then Some R8 else
        if ascii_dec c1 "9" then Some R9 else
        None
      | String c2 tl =>
        match tl with
        | EmptyString =>
          if ascii_dec c2 "X" then if ascii_dec c1 "A" then Some RAX else
          if ascii_dec c1 "B" then Some RBX else
          if ascii_dec c1 "C" then Some RCX else
          if ascii_dec c1 "D" then Some RDX else
          None else
          if ascii_dec c2 "P" then if ascii_dec c1 "S" then Some RSP else
          if ascii_dec c1 "B" then Some RBP else
          None else
          if ascii_dec c2 "I" then if ascii_dec c1 "S" then Some RSI else
          if ascii_dec c1 "D" then Some RDI else
          None else
          if ascii_dec c1 "1" then
            if ascii_dec c2 "0" then Some R10 else
            if ascii_dec c2 "1" then Some R11 else
            if ascii_dec c2 "2" then Some R12 else
            if ascii_dec c2 "3" then Some R13 else
            if ascii_dec c2 "4" then Some R14 else
            if ascii_dec c2 "5" then Some R15 else
            None else
          None
        | String _ _ => None
        end
      end
    | EmptyString => None
    end
    else None
  | EmptyString => None
  end.

Variant scale : Set := Scale1 | Scale2 | Scale4 | Scale8.

Definition word_of_scale (s: scale) :=
  I64.repr match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end.

Variant rflag : Set := CF | PF | ZF | SF | OF | DF.

Scheme Equality for rflag.
Definition rflag_eqP : Equality.axiom rflag_eq_dec.
Proof.
  move=> x y.
  case: rflag_eq_dec=> H; [exact: ReflectT|exact: ReflectF].
Qed.

Definition rflag_eqMixin := EqMixin rflag_eqP.
Canonical  rflag_eqType := EqType rflag rflag_eqMixin.

(* Pseudo-registers used in the intermediate language *)
Variant cond_flag : Set := EQ | CARRY | LTU | LTS | LEU | LES | GTU | GTS | GEU | GES.

Definition string_of_cond_flag (c: cond_flag) : string :=
  match c with
  | EQ => "EQ"
  | CARRY => "CARRY"
  | LTU => "LTU"
  | LTS => "LTS"
  | LEU => "LEU"
  | LES => "LES"
  | GTU => "GTU"
  | GTS => "GTS"
  | GEU => "GEU"
  | GES => "GES"
  end.

Definition cond_flag_of_string (s: string) :=
  match s with
  | String c0 (String c1 tl) =>
    match tl with
    | String c2 tl =>
      match tl with
      | String c3 (String c4 EmptyString) =>
        if (ascii_dec c0 "C" && ascii_dec c1 "A" && ascii_dec c2 "R"
         && ascii_dec c3 "R" && ascii_dec c4 "Y") then Some CARRY
        else None
      | EmptyString =>
        if ascii_dec c0 "L" then
          if ascii_dec c1 "T" then
            if ascii_dec c2 "U" then Some LTU
            else if ascii_dec c2 "S" then Some LTS
            else None
          else if ascii_dec c1 "E" then
            if ascii_dec c2 "U" then Some LEU
            else if ascii_dec c2 "S" then Some LES
            else None
          else None
        else if ascii_dec c0 "G" then
          if ascii_dec c1 "T" then
            if ascii_dec c2 "U" then Some GTU
            else if ascii_dec c2 "S" then Some GTS
            else None
          else if ascii_dec c1 "E" then
            if ascii_dec c2 "U" then Some GEU
            else if ascii_dec c2 "S" then Some GES
            else None
          else None
        else None
      | _ => None
      end
    | EmptyString =>
      if ascii_dec c0 "E" then if ascii_dec c1 "Q" then Some EQ
      else None
      else None
    end
  | _ => None
  end.

Scheme Equality for cond_flag.
Definition cond_flag_eqP : Equality.axiom cond_flag_eq_dec.
Proof.
  move=> x y.
  case: cond_flag_eq_dec=> H; [exact: ReflectT|exact: ReflectF].
Qed.

Definition cond_flag_eqMixin := EqMixin cond_flag_eqP.
Canonical  cond_flag_eqType := EqType cond_flag cond_flag_eqMixin.

Record address : Set := mkAddress {
  addrDisp : word ;
  addrBase : option register ;
  addrIndex : option (scale * register)
}.

Variant operand : Set :=
| Imm_op : word -> operand
| Reg_op : register -> operand
| Address_op : address -> operand.

Variant reg_or_immed : Set :=
| Reg_ri : register -> reg_or_immed
| Imm_ri : nat -> reg_or_immed.

Variant condition_type : Set :=
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

(* MMX syntax *)

(* Eight 64-bit mmx registers; mmx registers are syntactically
   different from fpu registers, but are semantically mapped
   to the same set of eight 80-bit registers as FPU registers *)
Definition mmx_register := nat.

Variant mmx_granularity : Set :=
| MMX_8                         (* 8 bits *)
| MMX_16                        (* 16 bits *)
| MMX_32                        (* 32 bits *)
| MMX_64.                       (* 64 bits *)

Variant mmx_operand : Set :=
| GP_Reg_op : register -> mmx_operand
| MMX_Addr_op : address -> mmx_operand
| MMX_Reg_op : mmx_register -> mmx_operand
| MMX_Imm_op : word -> mmx_operand.

(*SSE syntax *)
(* 8 128-bit registers (XMM0 - XMM7) introduced, along with MXCSR word for status and control of these registers *)
Definition sse_register := nat.

(*mmreg means mmx register. *)
Variant mxcsr: Set := FZ | Rpos | Rneg | RZ | RN | PM | UM | OM | ZM | DM | IM | DAZ | PE | UE |
			 OE | ZE | DE | IE.

Variant sse_operand : Set :=
| SSE_XMM_Reg_op : sse_register -> sse_operand
| SSE_MM_Reg_op : mmx_register -> sse_operand
| SSE_Addr_op : address -> sse_operand
| SSE_GP_Reg_op : register -> sse_operand (*r32 in manual*)
| SSE_Imm_op : word -> sse_operand.

(* The list of all instructions *)

Variant instr : Set :=
(* "High-level" assembly-specific instructions *)
| LABEL : label -> instr

| ADC   : forall (s:wsize)(op1 op2:operand), instr
| ADD   : forall (s:wsize)(op1 op2:operand), instr
| AND   : forall (s:wsize)(op1 op2:operand), instr
| BSF   : forall (op1 op2:operand), instr
| BSR   : forall (op1 op2:operand), instr
| BSWAP : forall (r:register), instr
| BT    : forall (op1 op2:operand), instr
| BTC   : forall (op1 op2:operand), instr
| BTR   : forall (op1 op2:operand), instr
| BTS   : forall (op1 op2:operand), instr
(*| CALL  : forall (near:bool)(absolute: bool)(op1:operand)(sel:option selector), instr*)
| CLC
| CLD
| CLI
| CMC
| CMOVcc : forall (ct:condition_type)(op1 op2: operand), instr
| CMP    : forall (s:wsize)(op1 op2:operand), instr
| CMPS   : forall (s:wsize), instr
| CMPXCHG: forall (s:wsize)(op1 op2:operand), instr
| CWD
| CWDE
| DEC   : forall (s:wsize)(op1:operand), instr
| DIV   : forall (s:wsize)(op1:operand), instr
| IDIV  : forall (s:wsize)(op1:operand), instr
| IMUL  : forall (s:wsize)(op1:operand) (opopt: option operand) (iopt:option nat), instr
| INC   : forall (s:wsize)(op1:operand), instr
| INVD  : instr
| INVLPG : forall (op1:operand), instr
| Jcc   : condition_type -> label -> instr
| JCXZ  : label -> instr
| JMP   : label -> instr
| LAHF
| LEA   : forall (op1 op2:operand), instr
| LODS  : forall (s:wsize), instr
| LOOP  : forall (disp:nat), instr
| LOOPZ : forall (disp:nat), instr
| LOOPNZ: forall (disp:nat), instr
| MOV   : forall (s:wsize)(op1 op2:operand), instr
| MOVBE : forall (op1 op2:operand), instr
| MOVS  : forall (s:wsize), instr
| MOVSX : forall (s:wsize)(op1 op2:operand), instr
| MOVZX : forall (s:wsize)(op1 op2:operand), instr
| MUL   : forall (s:wsize)(op1:operand), instr
| NEG   : forall (s:wsize)(op:operand), instr
| NOT   : forall (s:wsize)(op:operand), instr
| OR    : forall (s:wsize)(op1 op2:operand), instr
| POP   : forall (op1:operand), instr
| POPA
| POPF
| PUSH  : forall (s:wsize)(op1:operand), instr
| PUSHA
| PUSHF
| RCL   : forall (s:wsize)(op1:operand)(ri:reg_or_immed), instr
| RCR   : forall (s:wsize)(op1:operand)(ri:reg_or_immed), instr
(*| RET   : instr *)
| ROL   : forall (s:wsize)(op1:operand)(ri:reg_or_immed), instr
| ROR   : forall (s:wsize)(op1:operand)(ri:reg_or_immed), instr
| SAHF
| SAR   : forall (s:wsize)(op1:operand)(ri:reg_or_immed), instr
| SBB   : forall (s:wsize)(op1 op2:operand), instr
| SCAS  : forall (s:wsize), instr
| SETcc : forall (ct:condition_type)(op1:operand), instr
| SHL   : forall (s:wsize)(op1:operand)(ri:reg_or_immed), instr
| SHLD  : forall (op1:operand)(r:register)(ri:reg_or_immed), instr
| SHR   : forall (s:wsize)(op1:operand)(ri:reg_or_immed), instr
| SHRD  : forall (op1:operand)(r:register)(ri:reg_or_immed), instr
| STC
| STD
| STI
| STOS  : forall (s:wsize), instr
| SUB   : forall (s:wsize)(op1 op2:operand), instr
| TEST  : forall (s:wsize)(op1 op2:operand), instr
| WBINVD
| XADD  : forall (s:wsize)(op1 op2:operand), instr
| XCHG  : forall (s:wsize)(op1 op2:operand), instr
| XLAT
| XOR   : forall (s:wsize)(op1 op2:operand), instr

(* MMX instructions *)
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
(*| PMULHUW : forall  (op1 op2 : mmx_operand), instr*)
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

(* SSE instructions *)
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
| PMULHUW : forall (op1 op2: sse_operand), instr
| PSADBW : forall (op1 op2: sse_operand), instr
| PSHUFW : forall (op1 op2: sse_operand) (imm:nat), instr
| MASKMOVQ : forall (op1 op2: sse_operand), instr
| MOVNTPS : forall (op1 op2: sse_operand), instr
| MOVNTQ : forall (op1 op2: sse_operand), instr
| PREFETCHT0 : forall (op1: sse_operand), instr
| PREFETCHT1 : forall (op1: sse_operand), instr
| PREFETCHT2 : forall (op1: sse_operand), instr
| PREFETCHNTA : forall (op1: sse_operand), instr
| SFENCE: instr.

Definition cmd := seq instr.

Record xfundef := XFundef {
 xfd_stk_size : Z;
 xfd_nstk : register;
 xfd_arg  : seq register;
 xfd_body : cmd;
 xfd_res  : seq register;
}.

Definition xprog := seq (funname * xfundef).

(* ** Conversion to assembly *
 * -------------------------------------------------------------------- *)

Definition cond_flag_of_var_i (v: var_i) :=
  match v with
  | VarI (Var sbool s) _ => cond_flag_of_string s
  | _ => None
  end.

Definition reg_of_var ii (v: var_i) :=
  match v with
  | VarI (Var sword s) _ =>
     match (reg_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler ("Invalid register name: " ++ s))
     end
  | _ => cierror ii (Cerr_assembler "Invalid register type")
  end.

Definition reg_of_vars ii (vs: seq var_i) :=
  mapM (reg_of_var ii) vs.

Definition assemble_cond ii (e: pexpr) :=
  match e with
  | Pvar v =>
    match (cond_flag_of_var_i v) with
    | Some EQ => ciok E_ct
    | Some CARRY => ciok B_ct
    | Some LTU => ciok B_ct
    | Some LTS => ciok L_ct
    | Some LEU => ciok BE_ct
    | Some LES => ciok LE_ct
    | Some GTU => ciok NBE_ct
    | Some GTS => ciok NLE_ct
    | Some GEU => ciok NB_ct
    | Some GES => ciok NL_ct
    | None => cierror ii (Cerr_assembler "branching variable is not a valid cond_flag")
    end
  | _ => cierror ii (Cerr_assembler "invalid branching")
  end.

Definition word_of_int ii (z: Z) :=
  if (I64.signed (I64.repr z) == z) then
    ciok (I64.repr z)
  else
    cierror ii (Cerr_assembler "Integer constant out of bounds").

Definition word_of_pexpr ii e :=
  match e with
  | Pcast (Pconst z) => word_of_int ii z
  | _ => cierror ii (Cerr_assembler "Invalid integer constant")
  end.

Definition operand_of_lval ii (l: lval) :=
  match l with
  | Lnone _ => cierror ii (Cerr_assembler "Lnone not implemented")
  | Lvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_op s)
  | Lmem v e =>
     Let s := reg_of_var ii v in
     Let w := word_of_pexpr ii e in
     ciok (Address_op (mkAddress w (Some s) None))
  | Laset v e => cierror ii (Cerr_assembler "Laset not handled in assembler")
  end.

Definition operand_of_pexpr ii (e: pexpr) :=
  match e with
  | Pcast (Pconst z) =>
     Let w := word_of_int ii z in
     ciok (Imm_op w)
  | Pvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_op s)
  | Pload v e =>
     Let s := reg_of_var ii v in
     Let w := word_of_pexpr ii e in
     ciok (Address_op (mkAddress w (Some s) None))
  | _ => cierror ii (Cerr_assembler "Invalid pexpr")
  end.

Definition assemble_cond_opn ii (l: lval) (o: sopn) (e: pexprs) : ciexec instr :=
  match l with
  | Lvar vc =>
    match e with
    | [ :: e1; e2 ] =>
      Let o1 := operand_of_pexpr ii e1 in
      Let o2 := operand_of_pexpr ii e2 in
      match (cond_flag_of_var_i vc) with
      | Some rc =>
        match rc, o with
        | LTU, Oltu => ciok (CMP U64 o1 o2)
        | _, _ => cierror ii (Cerr_assembler "op not handled in condition")
        end
      | None => cierror ii (Cerr_assembler "invalid condition flag in LHS")
      end
    | _ => cierror ii (Cerr_assembler "invalid RHS in condition")
    end
  | _ => cierror ii (Cerr_assembler "invalid LHS in condition")
  end.

Definition assemble_i (li: linstr) : ciexec instr :=
  let (ii, i) := li in
  match i with
  | Lassgn l _ e =>
     Let dst := operand_of_lval ii l in
     Let src := operand_of_pexpr ii e in
     ciok (MOV U64 dst src)
  | Lopn l o p =>
     match l with
     | [:: a] => assemble_cond_opn ii a o p
     | _ => cierror ii (Cerr_assembler "not handling no/two lval for condition Copn")
     end
  | Llabel l => ciok (LABEL l)
  | Lgoto l => ciok (JMP l)
  | Lcond e l =>
     Let cond := assemble_cond ii e in
     ciok (Jcc cond l)
  end.

Definition assemble_c (lc: lcmd) : ciexec cmd :=
  mapM assemble_i lc.

Definition assemble_fd (fd: lfundef) :=
  Let fd' := assemble_c (lfd_body fd) in
  match (reg_of_string (lfd_nstk fd)) with
  | Some sp =>
    Let arg := reg_of_vars xH (lfd_arg fd) in
    Let res := reg_of_vars xH (lfd_res fd) in
    ciok (XFundef (lfd_stk_size fd) sp arg fd' res)
  | None => cierror xH (Cerr_assembler "Invalid stack pointer")
  end.

Definition assemble_prog (p: lprog) : cfexec xprog :=
  map_cfprog assemble_fd p.

