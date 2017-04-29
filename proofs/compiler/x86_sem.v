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
Require Import ZArith Setoid Morphisms.

From mathcomp Require Import all_ssreflect.
Require Export utils word low_memory memory linear expr x86.
Import Memory.
Import Ascii.
Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

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

