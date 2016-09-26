(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope seq_scope.

(* ** unrolling
 * -------------------------------------------------------------------- *)

Definition unroll_cmd (unroll_i: instr -> cmd) (c:cmd) : cmd := 
  List.fold_right (fun i c' => unroll_i i ++ c') [::] c.

Definition unroll_list dir vhi vlo :=
  let l := 
      if iword_leb vlo vhi then iota 0 (N.to_nat (iword_sub vhi vlo)).+1
      else [::] in
  let l := [seq (iword_add vlo (N.of_nat i)) | i <- l] in
  if dir is UpTo then l else rev l.

Fixpoint unroll_i (i:instr) : cmd := 
  match i with
  | Cbcmd _     => [::i]
  | Cif b c1 c2 => [::Cif b (unroll_cmd unroll_i c1) (unroll_cmd unroll_i c2)]
  | Cfor fi i (dir, low, hi) c => 
    let c' := unroll_cmd unroll_i c in
    if fi is Unroll_for then
      match is_const low, is_const hi with
      | Some vlo, Some vhi =>
        let l := unroll_list dir vhi vlo in
        let cs := map (fun n => assgn i (Pconst n) :: c') l in
        flatten cs 
      | _, _             => [::Cfor fi i (dir, low, hi) c']
      end
      
    else [::Cfor fi i (dir, low, hi) c']

  | Ccall ta tr x fd arg => [::Ccall x (unroll_call fd) arg]
  end

with unroll_call ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef ta tr p c r => 
    FunDef p (unroll_cmd unroll_i c) r
  end.

(* ** proofs
 * -------------------------------------------------------------------- *)

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

  Let Hbcmd : forall bc,  Pi (Cbcmd bc).
  Proof. move=> i s s' /=;apply: sem_seq1. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 s s' /= Hs;apply sem_seq1.
    inversion Hs;clear Hs;subst. apply (Eif H4)=> {H4}.
    case: cond H5=> [/Hc1 | /Hc2] //.
  Qed.

  Lemma iword_sub_to vhi vlo: (N.to_nat (iword_sub vhi vlo)) = (n2w vhi - n2w vlo)%N.
  Admitted.

  Lemma iword_add_to vhi vlo: (N.to_nat (iword_add vhi vlo)) = (n2w vhi + n2w vlo)%N.
  Admitted.

  Lemma n2w_Nofnat (x:nat) : x = n2w (N.of_nat x).
  Admitted.

  Lemma nat_of_bin_to_nat w : nat_of_bin w = N.to_nat w.
  Admitted.

  Let Hfor  : forall fi i rn c, Pc c -> Pi (Cfor fi i rn c).
  Proof.
    move=> fi i [[dir low] hi] c Hc s s' Hs /=.
    have Hs1 : sem s [:: Cfor fi i (dir, low, hi) (unroll_cmd unroll_i c)] s'.
    + apply sem_seq1. inversion Hs;clear Hs;subst.
      apply EFor with vlow vhi=> // => {H7 H8}.
      elim: H9 Hc=> {s s' vlow vhi c} [s iv c Hc| s1 s2 s3 iv w ws c Hs1 Hs2 Hrec Hc].
      + by constructor.
      by apply EForOne with s2;[apply Hc|apply Hrec].
    case: fi Hs Hs1=> //.
    case Heq1 : (is_const low) => [vlo| //].
    case Heq2 : is_const => [vhi| //] Hi;inversion Hi;clear Hi;subst.
    have ?:= is_constP Heq1;have ?:= is_constP Heq2;subst low hi=> {Heq1 Heq2}.
    move: H7 H8 => /= [] ? [] ?;subst.
    have Heq : [seq N.to_nat i| i <-  unroll_list dir vhi vlo ] =
            wrange dir  (n2w vlo) (n2w vhi).
    + rewrite /wrange /unroll_list iword_lebP.
      case Heq : (n2w vlo <= n2w vhi);last by case dir.
      case dir; rewrite ?map_rev -map_comp -(addn0 (n2w vlo)) iota_addl addn0 iword_sub_to.
      + by apply eq_map=> ? /=;rewrite iword_add_to -n2w_Nofnat.
      f_equal;by apply eq_map=> ? /=;rewrite iword_add_to -n2w_Nofnat.
    rewrite -Heq in H9 => {Heq} _.
    elim: unroll_list s H9=> [ | w ws Hrec] /= s Hf;inversion Hf;clear Hf;subst.
    + by constructor.
    apply Eseq with  {| emem := emem s; evm := write_rval (evm s) i (n2w (N.to_nat w)) |}.
    + by constructor => /=;rewrite nat_of_bin_to_nat.
    apply sem_app with s2;first by apply Hc.
    by apply Hrec.
  Qed.
    
  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hf s s' H;inversion H;clear H;subst => /=.
    unfold rarg in * => {rarg}.
    inversion H4;clear H4;subst;inversion H5;clear H5.
    inversion H6;clear H6;subst;inversion H0;clear H0;subst.
    case Heq: (sem_pexpr vm1 a) H7 H8 => [va /=|//] _ /Hf Hs.
    by apply sem_seq1;constructor;rewrite Heq.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x c re Hc mem mem' va vr H;inversion H;clear H;subst.
    inversion H0;clear H0;subst=> /=; constructor=> vm0.
    by case: (H7 vm0)=> vm2 /= [] /Hc Hc' Hvr;exists vm2. 
  Qed.

  Lemma unroll_callP ta tr (f : fundef ta tr) mem mem' va vr: 
    sem_call mem f va mem' vr -> sem_call mem (unroll_call f) va mem' vr.
  Proof.
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hcall Hfunc).
  Qed.

End PROOF.