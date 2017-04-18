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
Require Import low_memory memory sem linear compiler_util.
Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Definition selector := nat.

Inductive register : Set :=
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

Definition reg_of_string (s: string) :=
  match s with
  | "RAX"%string => Some RAX
  | "RCX"%string => Some RCX
  | "RDX"%string => Some RDX
  | "RBX"%string => Some RBX
  | "RSP"%string => Some RSP
  | "RBP"%string => Some RBP
  | "RSI"%string => Some RSI
  | "RDI"%string => Some RDI
  | "R8"%string => Some R8
  | "R9"%string => Some R9
  | "R10"%string => Some R10
  | "R11"%string => Some R11
  | "R12"%string => Some R12
  | "R13"%string => Some R13
  | "R14"%string => Some R14
  | "R15"%string => Some R15
  | _ => None
  end.

Inductive scale : Set := Scale1 | Scale2 | Scale4 | Scale8.

Definition word_of_scale (s: scale) :=
  I64.repr (match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end).

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
| Address_op : address -> operand.

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

(* MMX syntax *)

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

Inductive xsem1 (c:cmd) : x86_state -> x86_state -> Prop :=
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

Inductive xsem_fd P m1 fn va m2 vr : Prop := 
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
