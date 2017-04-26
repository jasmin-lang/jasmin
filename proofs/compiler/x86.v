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
Require Import Setoid Morphisms.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import ZArith.

Require Import strings word utils type var expr.
Require Import low_memory memory sem linear compiler_util.
Import Ascii.
Import Memory.
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

(* Sanity check *)
Lemma reg_of_string_of_register r : reg_of_string (string_of_register r) = Some r.
Proof. by case: r. Qed.

Definition Some_inj {A: Type} {a b: A} (H: Some b = Some a) : b = a :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Lemma reg_of_string_inj s1 s2 r :
  reg_of_string s1 = Some r ->
  reg_of_string s2 = Some r ->
  s1 = s2.
Proof.
  unfold reg_of_string; move=> A B; rewrite <- A in B.
  repeat match goal with
  | |- ?a = ?a => exact Logic.eq_refl
  | H : ?a = ?b |- _ => subst a || subst b || refine (let 'Logic.eq_refl := H in I)
  | H : Some _ = Some _ |- _ => apply Some_inj in H
  | H : (if is_left ?a then _ else _) = Some _ |- _ => destruct a; simpl in *
  | H : match ?a with _ => _ end = Some _ |- _ => destruct a; simpl in H
  end.
Qed.

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

Lemma cond_flag_of_string_of_cond_flag r : cond_flag_of_string (string_of_cond_flag r) = Some r.
Proof. by case: r. Qed.

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

(* ** Semantics of the assembly *
 * -------------------------------------------------------------------- *)

Definition is_label (lbl: label) (i:instr) : bool :=
  match i with
  | LABEL lbl' => lbl == lbl'
  | _ => false
  end.

Fixpoint find_label (lbl: label) (c: cmd) {struct c} : option cmd :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Module RegMap.
  Definition map := register -> word.

  Definition get (m: map) (x: register) := m x.

  Definition set (m: map) (x: register) (y: word) :=
    fun z => if (z == x) then y else m z.
End RegMap.

Module RflagMap.
  Definition map := rflag -> bool.

  Definition get (m: map) (x: rflag) := m x.

  Definition set (m: map) (x: rflag) (y: bool) :=
    fun z => if (z == x) then y else m z.
End RflagMap.

Notation regmap := RegMap.map.
Notation rflagmap := RflagMap.map.

Definition regmap0 : regmap := fun x => I64.repr 0.
Definition rflagmap0 : rflagmap := fun x => false.

Record x86_state := X86State {
  xmem : mem;
  xreg : regmap;
  xrf : rflagmap;
  xc : cmd
}.

Definition setc (s:x86_state) c := X86State s.(xmem) s.(xreg) s.(xrf) c.
Definition setrflags (s:x86_state) rf := X86State s.(xmem) s.(xreg) rf s.(xc).

Definition decode_addr (s: x86_state) (a: address) : word :=
  let (disp, base, ind) := a in
  match base, ind with
  | None, None => disp
  | Some r, None => I64.add disp (RegMap.get s.(xreg) r)
  | None, Some (sc, r) => I64.add disp (I64.mul (word_of_scale sc) (RegMap.get s.(xreg) r))
  | Some r1, Some (sc, r2) =>
     I64.add disp (I64.add (RegMap.get s.(xreg) r1) (I64.mul (word_of_scale sc) (RegMap.get s.(xreg) r2)))
  end.

Definition write_op (o: operand) (w: word) (s: x86_state) :=
  match o with
  | Imm_op v => type_error
  | Reg_op r => ok {| xmem := s.(xmem); xreg := RegMap.set s.(xreg) r w; xrf := s.(xrf); xc := s.(xc) |}
  | Address_op a =>
     let p := decode_addr s a in
     Let m := write_mem s.(xmem) p w in
     ok {| xmem := m; xreg := s.(xreg); xrf := s.(xrf); xc := s.(xc) |}
  end.

Definition write_ops xs vs s := fold2 ErrType write_op xs vs s.

Definition read_op (s: x86_state) (o: operand) :=
  match o with
  | Imm_op v => ok v
  | Reg_op r => ok (RegMap.get s.(xreg) r)
  | Address_op a =>
     let p := decode_addr s a in
     Let m := read_mem s.(xmem) p in
     ok m
  end.

Definition eval_cond (rm: rflagmap) (c: condition_type) :=
  let get := RflagMap.get rm in
  match c with
  | O_ct => get OF
  | NO_ct => ~~ get OF
  | B_ct => get CF
  | NB_ct => ~~ get CF
  | E_ct => get ZF
  | NE_ct => ~~ get ZF
  | BE_ct => get CF || get ZF
  | NBE_ct => ~~ get CF && ~~ get ZF
  | S_ct => get SF
  | NS_ct => ~~ get SF
  | P_ct => get PF
  | NP_ct => ~~ get PF
  | L_ct => get SF != get OF
  | NL_ct => get SF == get OF
  | LE_ct => get ZF || (get SF != get OF)
  | NLE_ct => get ZF && (get SF == get OF)
  end.

Definition SUB_rflags (s: x86_state) (o1 o2: operand) : exec rflagmap :=
  Let w1 := read_op s o1 in
  Let w2 := read_op s o2 in
  let sub := I64.sub w1 w2 in
  ok (fun rf =>
  match rf with
  | OF => I64.signed sub != w1 - w2
  | CF => I64.unsigned sub != w1 - w2
  | SF => I64.signed sub <? 0
  | PF => (I64.and sub I64.one) == I64.one
  | ZF => sub == I64.zero
  | _ => RflagMap.get s.(xrf) rf
  end)%Z.

Definition CMP_rflags := SUB_rflags.

Section XSEM.

Context (c: cmd).

Variant xsem1 : x86_state -> x86_state -> Prop :=
| XSem_LABEL s1 lbl cs:
    s1.(xc) = (LABEL lbl) :: cs ->
    xsem1 s1 (setc s1 cs)
| XSem_JMP s1 lbl cs cs':
    s1.(xc) = (JMP lbl) :: cs ->
    find_label lbl c = Some cs' ->
    xsem1 s1 (setc s1 cs')
| XSem_Jcc_true s1 cond lbl cs cs':
    s1.(xc) = (Jcc cond lbl) :: cs ->
    eval_cond s1.(xrf) cond = true ->
    find_label lbl c = Some cs' ->
    xsem1 s1 (setc s1 cs')
| XSem_Jcc_false s1 cond lbl cs:
    s1.(xc) = (Jcc cond lbl) :: cs ->
    eval_cond s1.(xrf) cond = false ->
    xsem1 s1 (setc s1 cs)
| XSem_MOV s1 dst src cs w s2:
    s1.(xc) = (MOV U64 dst src) :: cs ->
    read_op s1 src = ok w ->
    write_op dst w s1 = ok s2 ->
    xsem1 s1 (setc s2 cs)
| XSem_CMP s1 dst src rf cs:
    s1.(xc) = (CMP U64 dst src) :: cs ->
    CMP_rflags s1 dst src = ok rf ->
    xsem1 s1 (setc (setrflags s1 rf) cs).

Definition xsem : relation x86_state := clos_refl_trans _ xsem1.

Definition XSem0 s : xsem s s := rt_refl _ _ s.

Definition XSem1 s2 s1 s3 :
  xsem1 s1 s2 ->
  xsem s2 s3 ->
  xsem s1 s3.
Proof. by move=> H; apply: rt_trans; apply: rt_step. Qed.

End XSEM.

Record xfundef := XFundef {
 xfd_stk_size : Z;
 xfd_nstk : register;
 xfd_arg  : seq register;
 xfd_body : cmd;
 xfd_res  : seq register;
}.

Definition xprog := seq (funname * xfundef).

Variant xsem_fd P m1 fn va m2 vr : Prop :=
| XSem_fd : forall p cs fd vm2 rf m2' s1 s2,
    get_fundef P fn = Some fd ->
    alloc_stack m1 fd.(xfd_stk_size) = ok p ->
    let c := fd.(xfd_body) in
    write_op  (Reg_op fd.(xfd_nstk)) p.1 (X86State p.2 regmap0 rflagmap0 c) = ok s1 ->
    write_ops (map Reg_op fd.(xfd_arg)) va s1 = ok s2 ->
    xsem c s2 {| xmem := m2'; xreg := vm2; xrf := rf; xc := cs |} ->
    mapM (fun r => read_op {| xmem := m2'; xreg := vm2; xrf := rf; xc := cs |} (Reg_op r)) fd.(xfd_res) = ok vr ->
    m2 = free_stack m2' p.1 fd.(xfd_stk_size) ->
    xsem_fd P m1 fn va m2 vr.

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
     | None => cierror ii (Cerr_assembler "Invalid register name")
     end
  | _ => cierror ii (Cerr_assembler "Invalid register type")
  end.

Lemma cond_reg_of_var_disj ii v x r cf:
  reg_of_var ii v = ok r ->
  cond_flag_of_var_i x = Some cf ->
  ~ (v_var x = v_var v).
Proof.
  move: v=> [[[] vn] vi] //=.
  move: x=> [[[] vn'] vi'] //=.
Qed.

Lemma reg_of_var_ii ii1 ii2 v1 v2 r:
  v_var v1 = v_var v2 -> reg_of_var ii1 v1 = ok r -> reg_of_var ii2 v2 = ok r.
Proof.
  rewrite /reg_of_var.
  move: v1=> [[[] vn1] vt1] //.
  move: v2=> [[[] vn2] vt2] //.
  move=> [] <-.
  by case: (reg_of_string vn1).
Qed.

Lemma reg_of_var_inj ii v1 v2 r:
  reg_of_var ii v1 = ok r ->
  reg_of_var ii v2 = ok r ->
  v_var v1 = v_var v2.
Proof.
  rewrite /reg_of_var.
  move: v1=> [[[] vn1] vt1] //.
  move: v2=> [[[] vn2] vt2] //.
  case H1: (reg_of_string vn1)=> [r'1|//] []<-.
  case H2: (reg_of_string vn2)=> [r'2|//] [] H; subst r'2.
  by rewrite (reg_of_string_inj H1 H2).
Qed.

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

Lemma is_label_same a y lbl:
  assemble_i a = ok y ->
  linear.is_label lbl a = false ->
  is_label lbl y = false.
Proof.
  rewrite /linear.is_label.
  move: y=> -[] // l.
  move: a=> -[ii [lv t e|lv s e|l0|l0|e l0] //=].
  + apply: rbindP=> dst Hdst.
    by apply: rbindP=> src Hsrc.
  + move: lv=> -[] // a [] //.
    rewrite /assemble_cond_opn.
    move: a=> -[] // v.
    move: e=> -[] // e1 [] // e2 [] //.
    apply: rbindP=> z1 Hz1.
    apply: rbindP=> z2 Hz2.
    case: (cond_flag_of_var_i v)=> //.
    move=> [] //.
    by move: s=> [].
  + by move=> [] <-.
  + apply: rbindP=> //.
Qed.

Lemma find_label_same c c' lbl cs:
  assemble_c c = ok c' ->
  linear.find_label lbl c = Some cs ->
  exists cs', find_label lbl c' = Some cs' /\ assemble_c cs = ok cs'.
Proof.
  move=> Hc.
  elim: c c' Hc=> //= a l IH [|a' l'] // Hc.
  + rewrite /assemble_c /= in Hc.
    apply: rbindP Hc=> y Hy.
    by apply: rbindP.
  + rewrite /assemble_c /= in Hc.
    apply: rbindP Hc=> y Hy.
    rewrite -/(assemble_c _).
    apply: rbindP=> ys Hys -[]<- <-.
    case: ifP=> // H.
    + move=> -[]<-.
      exists ys; split=> //.
      move: a Hy H=> [ii [] //] l0 /= []<- /eqP -> /=.
      by rewrite eq_refl.
    + move=> Hfind.
      have [cs' [Hcs'1 Hcs'2]] := (IH _ Hys Hfind).
      exists cs'; split=> //=.
      by rewrite (is_label_same Hy).
Qed.

(* TODO: move *)
Lemma get_var_set_diff vm vm' x1 x2 w:
  set_var vm x1 w = ok vm' ->
  x1 <> x2 ->
  get_var vm x2 = get_var vm' x2.
Proof.
  move=> Hset Hneq.
  rewrite /get_var.
  suff ->: (vm.[x2] = vm'.[x2])%vmap=> //.
  apply: rbindP Hset=> z Hz []<-.
  rewrite Fv.setP_neq //.
  by apply/eqP.
Qed.

Lemma get_var_set_same vm vm' x w:
  set_var vm x w = ok vm' ->
  get_var vm' x = ok w.
Proof.
  apply: rbindP=> z Hz []<-.
  rewrite /get_var.
  rewrite Fv.setP_eq /=.
  move: x w z Hz=> [[]] //; try (by move=> vn [] z /= z0 // []<-).
  move=> p vn [] //= n a z.
  case Hle: (CEDecStype.pos_dec n p)=> [Heq|//].
  by subst p=> /= -[]<-.
Qed.

Section PROOF_CMD.
  Variable c: lcmd.
  Variable c': cmd.
  Hypothesis assemble_ok : assemble_c c = ok c'.

  Definition incl_regmap (vm: vmap) (rm: regmap) :=
    forall x ii r v, reg_of_var ii x = ciok r ->
    get_var vm x = ok v ->
    Vword (RegMap.get rm r) = v.

  Definition incl_rflagmap (vm: vmap) (rm: rflagmap) :=
    forall x cond v ii, assemble_cond ii (Pvar x) = ciok cond ->
    get_var vm x = ok v ->
    Vbool (eval_cond rm cond) = v.

  Definition incl_st (ls: lstate) (xs: x86_state) :=
    ls.(lmem) = xs.(xmem) /\ incl_regmap ls.(lvm) xs.(xreg)
                          /\ incl_rflagmap ls.(lvm) xs.(xrf)
                          /\ assemble_c ls.(lc) = ok xs.(xc).

  Lemma mem_addr_same ls xs (v0: var_i) s0 p ii w0 w1 w2 x1 x2:
    incl_st ls xs ->
    get_var (lvm ls) v0 = ok x1 ->
    to_word x1 = ok w1 ->
    sem_pexpr (to_estate ls) p = ok x2 ->
    to_word x2 = ok w2 ->
    reg_of_var ii v0 = ok s0 ->
    word_of_pexpr ii p = ok w0 ->
    I64.add w1 w2 = I64.add w0 (RegMap.get (xreg xs) s0).
  Proof.
    move=> [_ [Hreg _]] Hx1 Hw1 Hx2 Hw2 Hs0 Hw0.
    case: p Hx2 Hw0=> // -[] // z /= Hx2 Hw0.
    have Hx1' := Hreg _ _ _ _ Hs0 Hx1; subst x1.
    move: Hw1=> []->.
    move: Hx2=> [] Hx2.
    rewrite -{}Hx2 {x2} in Hw2.
    rewrite /word_of_int in Hw0.
    move: Hw0.
    case: ifP=> // _ []<-.
    move: Hw2=> [] ->.
    by rewrite I64.add_commut.
  Qed.

  Lemma pexpr_same s s' e v ii op:
    incl_st s s' ->
    sem_pexpr (to_estate s) e = ok v ->
    operand_of_pexpr ii e = ok op ->
    exists w, v = Vword w /\ read_op s' op = ok w.
  Proof.
    move=> Hincl.
    case: e=> //= [[] //| |].
    + move=> z.
      apply: rbindP=> z0.
      apply: rbindP=> /= x [] <- {x} [] <- {z0} []<- {v}.
      apply: rbindP=> w /= Hw []<- /=.
      exists (I64.repr z); split=> //.
      rewrite /word_of_int in Hw.
      move: Hw.
      by case: ifP=> // _ []<-.
    + move=> v0 Hv.
      move: Hincl=> [_ [Hreg _]].
      apply: rbindP=> s0 /Hreg /(_ Hv) Hv' []<- /=.
      subst v.
      eexists=> //.
    + move=> v0 p.
      apply: rbindP=> w1.
      apply: rbindP=> x1 Hx1 Hw1.
      apply: rbindP=> w2.
      apply: rbindP=> x2 Hx2 Hw2.
      apply: rbindP=> w Hw []<-.
      apply: rbindP=> s0 Hs0.
      apply: rbindP=> w0 Hw0 []<-.
      exists w; split=> //=.
      have Hincl' := Hincl.
      move: Hincl'=> [<- [Hreg _]].
      by rewrite -(mem_addr_same Hincl Hx1 Hw1 Hx2 Hw2 Hs0) // Hw.
  Qed.

  Lemma write_var_same w ls s' xs s v ii:
    incl_st ls xs ->
    write_var v (Vword w) (to_estate ls) = ok s' ->
    reg_of_var ii v = ok s ->
    exists xs', write_op (Reg_op s) w xs = ok xs' /\ incl_st (of_estate s' ls.(lc)) xs'.
  Proof.
    move=> Hincl Hw Hs; move: Hw.
    have [Hmem [Hreg [Hrf Hc]]] := Hincl.
    rewrite /write_var.
    apply: rbindP=> vm.
    apply: rbindP=> v0 Hv0 []<- []<-.
    eexists; split; eauto; repeat split=> //=.
    + move=> x ii0 r v' Hr.
      case Heq: (v_var x == v_var v).
      + move: Heq=> /eqP Heq.
        rewrite Heq.
        rewrite /get_var Fv.setP_eq /=.
        rewrite /RegMap.set /RegMap.get /=.
        rewrite (reg_of_var_ii _ Heq Hr) in Hs.
        move: Hs=> -[] <-.
        rewrite eq_refl.
        by case: (vtype v) v0 Hv0=> // v0 /= []<- []<-.
      + rewrite /get_var Fv.setP_neq /=.
        rewrite -/(get_var _ _)=> Hv'.
        move: Hincl=> [_ [/(_ x ii0 r _ Hr Hv') Hv _]].
        rewrite /RegMap.get /RegMap.set /=.
        case: eqP=> // Hr'; subst r.
        have Hx: v_var x = x by [].
        have Hr' := @reg_of_var_ii ii0 ii x x s Hx Hr.
        by rewrite (reg_of_var_inj Hs Hr') eq_refl in Heq.
        by rewrite eq_sym Heq.
    move=> x cf v' ii0 Hcf.
    case Heq: (v_var x == v_var v).
    + move: Heq=> /eqP Heq; exfalso.
      rewrite /assemble_cond in Hcf.
      case Hcf': (cond_flag_of_var_i x)=> [a|//].
      exact: (cond_reg_of_var_disj Hs Hcf').
      by rewrite Hcf' in Hcf.
    + rewrite /get_var Fv.setP_neq /= -/(get_var _ _).
      move=> Hv'.
      exact: (Hrf _ _ _ _ Hcf).
      by rewrite eq_sym Heq.
  Qed.

  Lemma write_vars_same w ls s' xs s (v: seq var_i) ii:
    incl_st ls xs ->
    write_vars v [seq (Vword i) | i <- w] (to_estate ls) = ok s' ->
    reg_of_vars ii v = ok s ->
    exists xs', write_ops (List.map Reg_op s) w xs = ok xs' /\ incl_st (of_estate s' ls.(lc)) xs'.
  Proof.
    elim: v w ls s xs=> [|va vl IH] [|wa wl] ls s xs Hincl //=.
    + move=> []<-.
      rewrite /reg_of_vars /= => -[]<-.
      by exists xs; split.
    + apply: rbindP=> x Ha Hl.
      rewrite /reg_of_vars /=.
      apply: rbindP=> y Hy.
      rewrite -/(reg_of_vars _ _).
      apply: rbindP=> ys Hys []<-.
      have [xs' [Hxs'1 Hxs'2]] := write_var_same Hincl Ha Hy.
      have Hx: x = to_estate (of_estate x ls.(lc)) by case: x Ha Hl Hxs'2.
      rewrite Hx in Hl.
      have [xs'' [Hxs''1 /= Hxs''2]] := IH _ _ _ _ Hxs'2 Hl Hys.
      exists xs''; repeat split=> //.
      move: Hxs'1=> -[] ->.
      exact: Hxs''1.
  Qed.

  Lemma lval_same ls s' xs l w op ii:
    incl_st ls xs ->
    write_lval l (Vword w) (to_estate ls) = ok s' ->
    operand_of_lval ii l = ok op ->
    exists xs', write_op op w xs = ok xs' /\ incl_st (of_estate s' ls.(lc)) xs'.
  Proof.
    move=> Hincl.
    case: l=> // [v|v e] /=.
    + move=> Hw.
      apply: rbindP=> s Hs []<-.
      exact: (write_var_same Hincl Hw Hs).
    + apply: rbindP=> w1; apply: rbindP=> x1 Hx1 Hw1.
      apply: rbindP=> w2; apply: rbindP=> x2 Hx2 Hw2.
      apply: rbindP=> m Hm []<-.
      apply: rbindP=> s Hs; apply: rbindP=> w0 Hw0 []<- /=.
      rewrite -(mem_addr_same Hincl Hx1 Hw1 Hx2 Hw2 Hs) //.
      move: Hincl=> [<- [Hr Hc]]; rewrite Hm /=.
      by eexists; split; eauto; split.
  Qed.

  Lemma read_vars_same res rres ls xs vr:
    incl_st ls xs ->
    reg_of_vars 1%positive res = ok rres ->
    mapM (fun x : var_i => get_var ls.(lvm) x) res = ok [seq (Vword i) | i <- vr] ->
    mapM (fun r => read_op xs (Reg_op r)) rres = ok vr.
  Proof.
    move=> Hincl.
    elim: res rres vr=> [|a l IH] rres vr /=.
    + rewrite /reg_of_vars /= => -[]<- [] /=.
      by move: vr=> [].
    + rewrite /reg_of_vars /=.
      apply: rbindP=> y Hy.
      rewrite -/(reg_of_vars _ _).
      apply: rbindP=> ys Hys -[]<-.
      apply: rbindP=> y0 Hy0.
      apply: rbindP=> ys0 Hys0 [].
      move: vr IH=> [] // va vl IH /= [] Hva Hvl.
      move: Hincl=> [_ [/(_ a _ _ _ Hy Hy0) Hy' _]].
      rewrite Hvl in Hys0.
      rewrite (IH _ _ Hys Hys0) /=.
      rewrite Hva in Hy'.
      by move: Hy'=> -[]<-.
  Qed.

  Lemma assemble_iP:
    forall s1 s2 s1', incl_st s1 s1' ->
    lsem1 c s1 s2 -> exists s2', xsem1 c' s1' s2' /\ incl_st s2 s2'.
  Proof.
    move=> s1 s2 s1' Hincl Hsem.
    have [Hmem [Hreg [Hrf Hc]]] := Hincl.
    sinversion Hsem.
    + apply: rbindP H0=> v Hv Hw.
      rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP=> dst Hdst.
      apply: rbindP=> src Hsrc []<-.
      apply: rbindP=> ys Hys [] Hxc.
      have [w [Hw1 Hw2]] := pexpr_same Hincl Hv Hsrc.
      rewrite Hw1 in Hw.
      have [xs' [Hxs'1 Hxs'2]] := lval_same Hincl Hw Hdst; eexists; split.
      apply: XSem_MOV; eauto.
      repeat split=> //=.
      by move: Hxs'2=> [? _].
      by move: Hxs'2=> [_ [? _]].
      by move: Hxs'2=> [_ [_ [? _]]].
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP H0=> v Hv Hw.
      move: xs H Hv Hw=> -[] // a [] //= H Hv Hw.
      rewrite /assemble_cond_opn.
      move: a H Hw=> [] // vc Hvc /= Hw.
      move: es Hv Hvc=> [] // e1 [] // e2 [] // Hv Hvc.
      apply: rbindP=> z1 Hz1; apply: rbindP=> z2 Hz2.
      case Hc: (cond_flag_of_var_i vc)=> [a|//].
      move: a Hc=> [] // Hc.
      move: o Hv Hvc=> -[] // Hv Hvc []<-.
      apply: rbindP=> ys Hys.
      move=> -[] Hxc.
      apply: rbindP Hv=> vs.
      rewrite /sem_pexprs /mapM /=.
      apply: rbindP=> v1 Hv1.
      apply: rbindP=> ys0; apply: rbindP=> v2 Hv2 []<- []<-.
      apply: rbindP=> w1 Hw1; apply: rbindP=> w2 Hw2 [] Hv; subst v.
      have [w1' [Hw1'1 Hw1'2]] := pexpr_same Hincl Hv1 Hz1.
      have [w2' [Hw2'1 Hw2'2]] := pexpr_same Hincl Hv2 Hz2.
      apply: rbindP Hw=> w'.
      apply: rbindP=> z Hz -[]<- []<-.
      eexists; split; eauto.
      apply: XSem_CMP.
      by rewrite -Hxc.
      rewrite /CMP_rflags /SUB_rflags Hw1'2 Hw2'2 //.
      repeat split=> //=.
      + move=> x' ii0 r v Hr Hv.
        apply: Hreg.
        exact: Hr.
        rewrite (get_var_set_diff Hz) //.
        exact: (cond_reg_of_var_disj Hr Hc).
      + move=> v.
        case Heq: (v_var v == v_var vc).
        + move: Heq=> /eqP Heq /= cond v' ii0.
          have ->: cond_flag_of_var_i v = cond_flag_of_var_i vc.
            rewrite /cond_flag_of_var_i.
            by move: v vc {Hc} Hvc Hz Heq=> [vv vi] [vcv vci] /= Hvc Hz ->.
          rewrite Hc=> -[]<- Hv.
          rewrite /eval_cond /RflagMap.get.
          rewrite Hw1'1 /= in Hw1; move: Hw1=> -[] Hw1; subst w1'.
          rewrite Hw2'1 /= in Hw2; move: Hw2=> -[] Hw2; subst w2'.
          have Hv': get_var z v = get_var z vc.
            by rewrite /get_var Heq.
          rewrite Hv' in Hv.
          have := get_var_set_same Hz; rewrite Hv; move=> -[]->.
          admit.
        + move=> cond v0 ii0 Hcond Hv0.
          have Hv: get_var (lvm s1) v = ok v0.
            rewrite (get_var_set_diff Hz) //.
            by apply/eqP; rewrite eq_sym Heq.
          have <- := Hrf v cond v0 ii0 Hcond Hv.
          admit.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> ys Hys [] Hc.
      eexists; split; eauto.
      apply: XSem_LABEL.
      by rewrite -Hc.
      by split.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> ys Hys [] Hc.
      have [cs'' [Hcs''1 Hcs''2]] := find_label_same assemble_ok H0.
      eexists; split; eauto.
      apply: XSem_JMP.
      by rewrite -Hc.
      exact: Hcs''1.
      by repeat split.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP=> cond Hcond []<-.
      apply: rbindP=> ys Hys [] Hi.
      have [cs'' [Hcs''1 Hcs''2]] := find_label_same assemble_ok H1.
      exists (X86State s1'.(xmem) s1'.(xreg) s1'.(xrf) cs''); split=> //=.
      apply: XSem_Jcc_true.
      by rewrite -Hi.
      move: e Hcond H0 {H}=> [] // v Hv /=.
      apply: rbindP=> -[] // b Hb []<-.
      by move: Hrf=> /(_ v _ _ _ Hv Hb) []<-.
      exact: Hcs''1.
    + rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y.
      apply: rbindP=> cond Hcond []<-.
      apply: rbindP=> ys Hys [] Hi.
      exists (X86State s1'.(xmem) s1'.(xreg) s1'.(xrf) ys); split=> //.
      apply: XSem_Jcc_false.
      by rewrite -Hi.
      move: e Hcond H0 {H}=> [] // v Hv /=.
      apply: rbindP=> -[] // b Hb []<-.
      by move: Hrf=> /(_ v _ _ _ Hv Hb) []<-.
  Admitted.

  Lemma assemble_cP:
    forall s1 s2 s1', incl_st s1 s1' ->
    lsem c s1 s2 -> exists s2', xsem c' s1' s2' /\ incl_st s2 s2'.
  Proof.
    move=> s1 s2 s1' Hincl H.
    move: s1' Hincl.
    elim H using lsem_ind; clear -assemble_ok.
    + move=> s s1'; exists s1'=> //; split=> //; exact: XSem0.
    + move=> s1 s2 s3 H _ IH s1' Hincl; have [s2' [Hs2'1 Hs2'2]] := (assemble_iP Hincl H).
      have [s3' [Hs3'1 Hs3'2]] := (IH _ Hs2'2).
      exists s3'; split=> //.
      apply: XSem1; [exact: Hs2'1|exact: Hs3'1].      
  Qed.
End PROOF_CMD.

(* TODO: move *)
Lemma get_var_vmap0 x v:
  (vtype x == sbool) || (vtype x == sint) || (vtype x == sword) ->
  ~ get_var vmap0 x = ok v.
Proof.
  move=> Ht.
  rewrite /get_var /vmap0.
  apply: rbindP=> v' Habs _.
  rewrite /Fv.empty /Fv.get /= /undef_addr {v} in Habs.
  by move: x v' Habs Ht=> [[] vx] vn.
Qed.

Section PROOF.
  Variable p: lprog.
  Variable p': xprog.
  Hypothesis assemble_ok : assemble_prog p = ok p'.

  Lemma assemble_fdP:
    forall fn m1 va m2 vr,
    lsem_fd p m1 fn (map Vword va) m2 (map Vword vr) -> xsem_fd p' m1 fn va m2 vr.
  Proof.
    move=> fn m1 va m2 vr H.
    sinversion H.
    have H0' := assemble_ok.
    rewrite /assemble_prog in H0'.
    have [f' [Hf'1 Hf'2]] := get_map_cfprog H0' H0.
    apply: rbindP Hf'1=> c' Hc'.
    case Hsp: (reg_of_string _)=> [sp|//].
    apply: rbindP=> arg Harg.
    apply: rbindP=> res Hres.
    move=> [] Hf'.
    rewrite -{}Hf' in Hf'2.
    have Hs: {| emem := p0.2; evm := vmap0 |} = to_estate (Lstate p0.2 vmap0 c) by [].
    rewrite Hs in H2.
    have Hsp': reg_of_var xH {| v_var := {| vtype := sword; vname := lfd_nstk fd |}; v_info := 1%positive |} = ok sp.
      by rewrite /= Hsp.
    have Hincl0: incl_st {| lmem := p0.2; lvm := vmap0; lc := c |} {| xmem := p0.2; xreg := regmap0; xrf := rflagmap0; xc := c' |}.
      repeat split=> //=.
      move=> x ii r v Hr Habs; exfalso.
      apply: (get_var_vmap0 _ Habs).
      by move: x Hr Habs=> [[[] vn] vi].
      move=> x cond v ii Hcond Habs; exfalso.
      apply: (get_var_vmap0 _ Habs).
      by move: x Hcond Habs=> [[[] vn] vi].
    have [xs1 /= [[] Hxs11 Hxs12]] := write_var_same Hincl0 H2 Hsp'.
    have Hs1: s1 = to_estate (of_estate s1 c).
      by case: s1 H3 H2 Hxs12.
    rewrite Hs1 in H3.
    have [xs2 /= [Hxs21 Hxs22]] := write_vars_same Hxs12 H3 Harg.
    have [xs3 /= [Hxs31 Hxs32]] := assemble_cP Hc' Hxs22 H4.
    have Hres' := (read_vars_same Hxs32 Hres H5).
    move: xs3 Hxs31 Hxs32 Hres'=> [xmem3 xreg3 xrf3 xc3] Hxs31 Hxs32 Hres' /=.
    apply: (XSem_fd Hf'2 H1)=> /=.
    by rewrite -Hxs11.
    exact: Hxs21.
    exact: Hxs31.
    exact: Hres'.
    by move: Hxs32=> [] /= ->.
  Qed.

End PROOF.
