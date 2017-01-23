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

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import ZArith.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr 
               memory dmasm_sem compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

(* ** unrolling
 * -------------------------------------------------------------------- *)

Definition unroll_cmd (unroll_i: instr -> cmd) (c:cmd) : cmd := 
  List.fold_right (fun i c' => unroll_i i ++ c') [::] c.

Definition assgn ii x e := MkI ii (Cassgn (Rvar x) AT_inline e).

Fixpoint unroll_i (i:instr) : cmd := 
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ => [:: i ]
  | Copn   _ _ _ => [:: i ]
  | Cif b c1 c2  => [:: MkI ii (Cif b (unroll_cmd unroll_i c1) (unroll_cmd unroll_i c2)) ]
  | Cfor i (dir, low, hi) c => 
    let c' := unroll_cmd unroll_i c in
    match is_const low, is_const hi with
    | Some vlo, Some vhi =>
      let l := wrange dir (I64.repr vlo) (I64.repr vhi) in
      let cs := map (fun n => assgn ii i (Pconst n) :: c') l in
      flatten cs 
    | _, _       => [:: MkI ii (Cfor i (dir, low, hi) c') ]
    end     
  | Cwhile e c   => [:: MkI ii (Cwhile e (unroll_cmd unroll_i c)) ]
  | Ccall _ _ _ _  => [:: i ]
  end.

Definition unroll_fun (f:funname * fundef) :=
  let (ii,p,c,r) := f.2 in
  (f.1, MkFun ii p (unroll_cmd unroll_i c) r).

Definition unroll_prog (p:prog) := map unroll_fun p.

(* ** proofs
 * -------------------------------------------------------------------- *)

(*
Section PROOF.

  Let Pi (i:instr) := 
    forall s s', sem_i s i s' -> sem s (unroll_i i) s'.

  Let Pc (c:cmd) := 
    forall s s', sem s c s' -> sem s (unroll_cmd unroll_i c) s'.

  Let Pf ta tr (fd:fundef ta tr) := 
    forall mem mem' va vr, 
    sem_call mem fd va mem' vr ->
    sem_call mem (unroll_call fd) va mem' vr.

  Let Hskip : Pc [::].
  Proof. by move=> s s' H. Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc s s' H;inversion H;clear H;subst=> /=.
    by apply: sem_app (Hi _ _ H3) (Hc _ _ H5).
  Qed.

  Let Hbcmd : forall t (x:rval t) e,  Pi (Cassgn x e).
  Proof. move=> i s s' /=;apply: sem_seq1. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 s s' /= Hs;apply sem_seq1.
    inversion Hs;clear Hs;subst. apply (Eif H4)=> {H4}.
    case: cond H5=> [/Hc1 | /Hc2] //.
  Qed.

  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i [[dir low] hi] c Hc s s' Hs /=.
    have Hs1 : sem s [:: Cfor i (dir, low, hi) (unroll_cmd unroll_i c)] s'.
    + apply sem_seq1. inversion Hs;clear Hs;subst.
      apply EFor with vlow vhi=> // => {H6 H7}.
      elim: H8 Hc=> {s s' vlow vhi c} [s iv c Hc| s1 s1' s2 s3 iv w ws c Hw Hs1 Hs2 Hrec Hc].
      + by constructor.
      by apply EForOne with s1' s2 => //;[apply Hc|apply Hrec].
    case Heq1 : (is_const low) => [vlo| //].
    case Heq2 : is_const => [vhi| //];inversion Hs;clear Hs;subst.
    have ?:= is_constP Heq1;have ?:= is_constP Heq2;subst low hi=> {Heq1 Heq2}.
    move: H6 H7 => /= [] ? [] ?;subst=> {Hs1}.
    elim: wrange s H8=> [ | w ws Hrec] /= s Hf;inversion Hf;clear Hf;subst.
    + by constructor.
    apply Eseq with  s1'.
    + by constructor.
    apply sem_app with s2;first by apply Hc.
    by apply Hrec.
  Qed.

  Let Hwhile : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e c Hc s s' Hs /=.
    apply sem_seq1;inversion Hs;clear Hs;subst;constructor.
    elim: H3 Hc => {s s' e c} [s e c He | s1 s2 s3 e c He Hc Hw Hrec] HP.
    + by apply EWhileDone. 
    by apply EWhileOne with s2=> //;[apply HP | apply Hrec].
  Qed.

  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hf s s' H;sinversion H => /=.
    sinversion H2;sinversion H5;sinversion H6;sinversion H0.
    unfold rarg in * => {rarg}.
    case Heq: (sem_pexpr _ a) H7 H8 => [va /=|//] _ /Hf Hs.
    by apply sem_seq1;econstructor;eauto;rewrite Heq.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x c re Hc mem mem' va vr H;sinversion H.
    sinversion H0=> /=; constructor=> //= vm0 Hvm0.
    by case: (H6 vm0 Hvm0)=> vm2 /= [] vm1 [] ? /Hc Hc' Hvr;exists vm2, vm1. 
  Qed.

  Lemma unroll_callP ta tr (f : fundef ta tr) mem mem' va vr: 
    sem_call mem f va mem' vr -> 
    sem_call mem (unroll_call f) va mem' vr.
  Proof.
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
  Qed.

End PROOF.
*)