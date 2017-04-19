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

Variant scale : Set := Scale1 | Scale2 | Scale4 | Scale8.

Definition word_of_scale (s: scale) :=
  I64.repr match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end.

Variant rflag : Set := CF | PF | AF | ZF | SF | OF.

Definition string_of_rflag (r: rflag) : string :=
  match r with
  | CF => "CF"
  | PF => "PF"
  | AF => "AF"
  | ZF => "ZF"
  | SF => "SF"
  | OF => "OF"
  end%string.

Definition rflag_of_string (s: string) :=
  match s with
  | String c0 (String c1 EmptyString) =>
    if ascii_dec c1 "F" then
      if ascii_dec c0 "C" then Some CF else
      if ascii_dec c0 "P" then Some PF else
      if ascii_dec c0 "A" then Some AF else
      if ascii_dec c0 "Z" then Some ZF else
      if ascii_dec c0 "S" then Some SF else
      if ascii_dec c0 "O" then Some OF else
      None else
    None
  | _ => None
  end.

Lemma rflag_of_string_of_rflag r : rflag_of_string (string_of_rflag r) = Some r.
Proof. by case: r. Qed.

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
    fun z => if (x == z) then y else m x.
End RegMap.

Notation regmap := RegMap.map.

Definition regmap0 : regmap := fun x => I64.repr 0.

Record x86_state := X86State {
  xmem : mem;
  xreg : regmap;
  xc : cmd
}.

Definition setc (s:x86_state) c := X86State s.(xmem) s.(xreg) c.

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
  | Reg_op r => ok {| xmem := s.(xmem); xreg := RegMap.set s.(xreg) r w; xc := s.(xc) |}
  | Address_op a =>
     let p := decode_addr s a in
     Let m := write_mem s.(xmem) p w in
     ok {| xmem := m; xreg := s.(xreg); xc := s.(xc) |}
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

Variant xsem1 (c:cmd) : x86_state -> x86_state -> Prop :=
| XSem_LABEL s1 lbl cs:
    s1.(xc) = (LABEL lbl) :: cs ->
    xsem1 c s1 (setc s1 cs)
| XSem_JMP s1 lbl cs cs':
    s1.(xc) = (JMP lbl) :: cs ->
    find_label lbl c = Some cs' ->
    xsem1 c s1 (setc s1 cs')
| XSem_MOV s1 dst src cs w s2:
    s1.(xc) = (MOV U64 dst src) :: cs ->
    read_op s1 src = ok w ->
    write_op dst w s1 = ok s2 ->
    xsem1 c s1 (setc s2 cs).

Inductive xsem (c:cmd) : x86_state -> x86_state -> Prop:=
| XSem0 : forall s, xsem c s s
| XSem1 : forall s1 s2 s3, xsem1 c s1 s2 -> xsem c s2 s3 -> xsem c s1 s3.

Record xfundef := XFundef {
 xfd_stk_size : Z;
 xfd_nstk : register;
 xfd_arg  : seq register;
 xfd_body : cmd;
 xfd_res  : seq register;
}.

Definition xprog := seq (funname * xfundef).

Variant xsem_fd P m1 fn va m2 vr : Prop :=
| XSem_fd : forall p cs fd vm2 m2' s1 s2,
    get_fundef P fn = Some fd ->
    alloc_stack m1 fd.(xfd_stk_size) = ok p ->
    let c := fd.(xfd_body) in
    write_op  (Reg_op fd.(xfd_nstk)) p.1 (X86State p.2 regmap0 [::]) = ok s1 ->
    write_ops (map Reg_op fd.(xfd_arg)) va s1 = ok s2 ->
    xsem c s2 {| xmem := m2'; xreg := vm2; xc := cs |} ->
    mapM (fun r => read_op {| xmem := m2'; xreg := vm2; xc := cs |} (Reg_op r)) fd.(xfd_res) = ok vr ->
    m2 = free_stack m2' p.1 fd.(xfd_stk_size) ->
    xsem_fd P m1 fn va m2 vr.

(* ** Conversion to assembly *
 * -------------------------------------------------------------------- *)

Definition rflag_of_var_i (v: var_i) :=
  match v with
  | VarI (Var sbool s) _ => rflag_of_string s
  | _ => None
  end.

Definition reg_of_var_i ii (v: var_i) :=
  match v with
  | VarI (Var sword s) _ =>
     match (reg_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler "Invalid register name")
     end
  | _ => cierror ii (Cerr_assembler "Invalid register type")
  end.

Fixpoint reg_of_vars_i ii (vs: list var_i) :=
  mapM (reg_of_var_i ii) vs.

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
     Let s := reg_of_var_i ii v in
     ciok (Reg_op s)
  | Lmem v e =>
     Let s := reg_of_var_i ii v in
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
     Let s := reg_of_var_i ii v in
     ciok (Reg_op s)
  | Pload v e =>
     Let s := reg_of_var_i ii v in
     Let w := word_of_pexpr ii e in
     ciok (Address_op (mkAddress w (Some s) None))
  | _ => cierror ii (Cerr_assembler "Invalid pexpr")
  end.

Definition assemble_i (li: linstr) : ciexec instr :=
  let (ii, i) := li in
  match i with
  | Lassgn l _ e =>
     Let dst := operand_of_lval ii l in
     Let src := operand_of_pexpr ii e in
     ciok (MOV U64 dst src)
  | Lopn l o p => cierror ii (Cerr_assembler "opn")
  | Llabel l => ciok (LABEL l)
  | Lgoto l => ciok (JMP l)
  | Lcond e l =>
     Let cond := assemble_cond ii e in
     ciok (Jcc cond l)
  | Lreturn => ciok (LABEL xH)
  end.

Definition assemble_c (lc: lcmd) : ciexec cmd :=
  mapM assemble_i lc.

Definition assemble_fd (fd: lfundef) :=
  Let fd' := assemble_c (lfd_body fd) in
  match (reg_of_string (lfd_nstk fd)) with
  | Some sp =>
    Let arg := reg_of_vars_i xH (lfd_arg fd) in
    Let res := reg_of_vars_i xH (lfd_res fd) in
    ciok (XFundef (lfd_stk_size fd) sp arg fd' res)
  | None => cierror xH (Cerr_assembler "Invalid stack pointer")
  end.

Definition assemble_prog (p: lprog) : cfexec xprog :=
  map_cfprog assemble_fd p.

(*
Section RECT.
  Variables (Pr:linstr_r -> Type) (Pi:linstr -> Type) (Pc : lcmd -> Type).
  Hypothesis Hmk  : forall i ii, Pr i -> Pi (MkLI ii i).
  Hypothesis Hnil : Pc [::].
  Hypothesis Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hasgn: forall x t e, Pr (Lassgn x t e).
  Hypothesis Hopn : forall xs o es, Pr (Lopn xs o es).
  Hypothesis Hlbl : forall l, Pr (Llabel l).
  Hypothesis Hgoto: forall l, Pr (Lgoto l).
  Hypothesis Hcond: forall e l, Pr (Lcond e l).
  Hypothesis Hret : Pr Lreturn.

  Definition linstr_r_Rect (i:linstr_r) : Pr i :=
    match i return Pr i with
    | Lassgn x t e => Hasgn x t e
    | Lopn xs o es => Hopn xs o es
    | Llabel l => Hlbl l
    | Lgoto l => Hgoto l
    | Lcond e l => Hcond e l
    | Lreturn => Hret
    end.

  Definition linstr_Rect (i:linstr) : Pi i :=
    match i return Pi i with
    | MkLI ii i => @Hmk i ii (linstr_r_Rect i)
    end.

  Fixpoint lcmd_rect (c:lcmd) : Pc c :=
    match c return Pc c with
    | [::] => Hnil
    | i::c => @Hcons i c (linstr_Rect i) (lcmd_rect c)
    end.
End RECT.
*)

Section PROOF_CMD.
  Variable c: lcmd.
  Variable c': cmd.
  Hypothesis assemble_ok : assemble_c c = ok c'.

  Definition incl_regmap (vm: vmap) (rm: regmap) :=
    forall x ii r, reg_of_var_i ii x = ciok r ->
    get_var vm x = ok (Vword (RegMap.get rm r)).

  Definition incl_st (ls: lstate) (xs: x86_state) :=
    ls.(lmem) = xs.(xmem) /\ incl_regmap ls.(lvm) xs.(xreg) /\ assemble_c ls.(lc) = ok xs.(xc).

(*
  Definition Pr (i_r: linstr_r) := forall s1 s2 s1',
    incl_st s1 s1' ->
    lsem1 c s1 s2 -> exists s2', xsem1 c' s1' s2'.

  Lemma assemble_cP lc xc:
    assemble_c lc = ok xc ->
    forall m vm rm m' vm', lsem lc (Lstate m vm lc) (Lstate m' vm' [::]) ->
    incl_regmap vm rm ->
    exists rm', xsem xc (X86State m rm xc) (X86State m' rm' [::]).
  Proof.
    elim: lc=> //=.
    + rewrite /assemble_c /= => -[] <- m vm rm m' vm' H.
      sinversion H.
  Admitted.
*)

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
      apply: rbindP=> s0 /Hreg Hv' []<- /=.
      rewrite Hv' in Hv.
      move: Hv=> []<-.
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
      move: Hincl=> [<- [Hreg _]].
      case: p Hx2 Hw0=> // -[] // z /= Hx2 Hw0.
      rewrite (Hreg _ _ _ Hs0) in Hx1.
      move: Hx1=> [] Hx1.
      subst x1.
      move: Hw1=> []->.
      move: Hx2=> [] Hx2.
      rewrite -{}Hx2 {x2} in Hw2.
      rewrite /word_of_int in Hw0.
      move: Hw0.
      case: ifP=> // _ []<-.
      move: Hw2=> [] ->.
      by rewrite I64.add_commut Hw.
  Qed.

  Lemma assemble_iP:
    forall s1 s2 s1', incl_st s1 s1' ->
    lsem1 c s1 s2 -> exists s2', xsem1 c' s1' s2' /\ incl_st s2 s2'.
  Proof.
    move=> s1 s2 s1' Hincl Hsem.
    have [Hmem [Hreg Hc]] := Hincl.
    sinversion Hsem.
    + apply: rbindP H0=> v Hv Hw.
      rewrite H /= /assemble_c /= in Hc.
      apply: rbindP Hc=> y; apply: rbindP=> dst Hdst.
      apply: rbindP=> src Hsrc [] <-.
      rewrite -/(assemble_c _).
      apply: rbindP=> ys Hys [] Hxc.
      have [w [Hw1 Hw2]] := (pexpr_same Hincl Hv Hsrc).
      admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  Admitted.

  Lemma assemble_cP:
    forall s1 s2 s1', incl_st s1 s1' ->
    lsem c s1 s2 -> exists s2', xsem c' s1' s2'.
  Proof.
    move=> s1 s2 s1' Hincl H.
    move: s1' Hincl.
    induction H.
    + move=> s1'; exists s1'=> //; exact: XSem0.
    + move=> s1' Hincl; have [s2' [Hs2'1 Hs2'2]] := (assemble_iP Hincl H).
      have [s3' Hs3'] := (IHlsem _ Hs2'2).
      exists s3'.
      apply: XSem1; [exact: Hs2'1|exact: Hs3'].
  Qed.
End PROOF_CMD.

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
    have [f' [Hf'1 Hf'2]] : exists f', assemble_fd fd = ok f' /\ get_fundef p' fn = Some f'.
      admit. (* get_map_cfprog: need an eqType.. *)
    apply: rbindP Hf'1=> z Hz.
    case: (reg_of_string _)=> // sp.
    apply: rbindP=> arg Harg.
    apply: rbindP=> res Hres.
    move=> [] Hf'.
    rewrite -{}Hf' in Hf'2.
    apply: (XSem_fd Hf'2 H1)=> //=.
    admit.
    admit.
    admit.
  Admitted.
End PROOF.
