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

(* --------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
Require Import Setoid Morphisms ZArith.
Require Import gen_map word utils type var expr low_memory sem Ssem.

Import UnsafeMemory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope svmap_scope.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear sfor_nilI with
  (forall p x P c Q, ssem_for p x [::] P c Q) Sort Prop.
  
Derive Inversion_clear sfor_consI with
  (forall p x z zs P c Q, ssem_for p x (z :: zs) P c Q) Sort Prop.

(* -------------------------------------------------------------------- *)
Scheme _ssem_Ind      := Induction for ssem      Sort Prop
with   _ssem_i_Ind    := Induction for ssem_i    Sort Prop
with   _ssem_I_Ind    := Induction for ssem_I    Sort Prop
with   _ssem_for_Ind  := Induction for ssem_for  Sort Prop
with   _ssem_call_Ind := Induction for ssem_call Sort Prop.

Section SsemInd.

Variables (p : prog).
Notation gd := (p_globs p).

Variables
  (Pc   : sestate -> cmd -> sestate -> Prop)
  (Pi_r : sestate -> instr_r -> sestate -> Prop)
  (Pi   : sestate -> instr -> sestate -> Prop)
  (Pfor : var -> seq Z -> sestate -> cmd -> sestate -> Prop)
  (Pfun : mem -> funname -> seq svalue -> mem -> seq svalue -> Prop).

Hypothesis Inil : forall s, Pc s [::] s.

Hypothesis Icons : forall s1 s2 s3 i c,
     ssem_I p s1 i s2 -> Pi s1 i s2
  -> ssem p s2 c s3 -> Pc s2 c s3
  -> Pc s1 (i :: c) s3.

Hypothesis ImkI : forall ii i s1 s2,
  ssem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

(*Hypothesis Iasgn : forall s1 s2 x tag e,
  Let v := ssem_pexpr gd s1 e in swrite_lval gd x v s1 = ok s2 ->
  Pi_r s1 (Cassgn x tag e) s2.*)

Hypothesis Iopn : forall s1 s2 t o xs es,
     Let x :=
       Let x := ssem_pexprs gd s1 es in ssem_sopn o x
     in swrite_lvals gd s1 xs x = ok s2
  -> Pi_r s1 (Copn xs t o es) s2.

Hypothesis Iif_true : forall s1 s2 e c1 c2,
  Let x := ssem_pexpr gd s1 e in sto_bool x = ok true ->
  ssem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

Hypothesis Iif_false : forall s1 s2 e c1 c2,
  Let x := ssem_pexpr gd s1 e in sto_bool x = ok false ->
  ssem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

Hypothesis Iwhile_true : forall s1 s2 s3 s4 c e c',
     ssem p s1 c s2 -> Pc s1 c s2
  -> Let x := ssem_pexpr gd s2 e in sto_bool x = ok true
  -> ssem p s2 c' s3 -> Pc s2 c' s3
  -> ssem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4
  -> Pi_r s1 (Cwhile c e c') s4.

Hypothesis Iwhile_false : forall s1 s2 c e c',
     ssem p s1 c s2 -> Pc s1 c s2
  -> Let x := ssem_pexpr gd s2 e in sto_bool x = ok false
  -> Pi_r s1 (Cwhile c e c') s2.

Hypothesis Ifor : forall s1 s2 (i : var_i) d lo hi c vlo vhi,
     Let x := ssem_pexpr gd s1 lo in sto_int x = ok vlo
  -> Let x := ssem_pexpr gd s1 hi in sto_int x = ok vhi
  -> ssem_for p i (wrange d vlo vhi) s1 c s2
  -> Pfor i (wrange d vlo vhi) s1 c s2
  -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

Hypothesis Ifor_nil : forall s i c, Pfor i [::] s c s.

Hypothesis Ifor_cons : forall s1 s1' s2 s3 i (w : Z) ws c,
     swrite_var i w s1 = ok s1'
  -> ssem p s1' c s2 -> Pc s1' c s2
  -> ssem_for p i ws s2 c s3 -> Pfor i ws s2 c s3
  -> Pfor i (w :: ws) s1 c s3.

Hypothesis Icall : forall s1 (m2 : mem) s2 ii xs fn args vargs vs,
     ssem_pexprs gd s1 args = ok vargs
  -> ssem_call p s1.(semem) fn vargs m2 vs
  -> Pfun s1.(semem) fn vargs m2 vs
  -> swrite_lvals gd {| semem := m2; sevm := s1.(sevm) |} xs vs = ok s2
  -> Pi_r s1 (Ccall ii xs fn args) s2.

Hypothesis Iproc : forall m1 m2 fn f vargs s1 vm2 vres,
     get_fundef (p_funcs p) fn = Some f
  -> swrite_vars (f_params f) vargs {| semem := m1; sevm := svmap0 |} = ok s1
  -> ssem p s1 (f_body f) {| semem := m2; sevm := vm2 |}
  -> Pc s1 (f_body f) {| semem := m2; sevm := vm2 |}
  -> [seq sget_var vm2 x | x : var_i <- f_res f] = vres
  -> Pfun m1 fn vargs m2 vres.

(*Lemma ssem_Ind s1 c s2 : ssem p gd s1 c s2 -> Pc s1 c s2.
Proof.
by apply/(@_ssem_Ind p gd
           (fun s1 c s2 _ => Pc s1 c s2)
           (fun s1 i s2 _ => Pi_r s1 i s2)
           (fun s1 i s2 _ => Pi s1 i s2)
           (fun x sz s1 c s2 _ => Pfor x sz s1 c s2)
           (fun m f l m' l' _  => Pfun m f l m' l')); auto.
Qed.*)
End SsemInd.

(* --------------------------------------------------------------------- *)
Lemma surj_SEstate s : {| semem := semem s; sevm := sevm s |} = s.
Proof. by case: s. Qed.
  
Definition svmap_eq_except (s : Sv.t) (vm1 vm2 : svmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (svmap_eq_except s vm1 vm2)
  (at level 70, vm2 at next level,
    format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'") : svmap_scope.

Lemma svmap_eq_except_trans vm2 vm1 vm3 s:
  vm1 = vm2 [\s] -> vm2 = vm3 [\s] -> vm1 = vm3 [\s].
Proof. by move=> h1 h2 x xin; rewrite h1 ?h2. Qed.

Lemma svmap_eq_except_subset s1 s2 vm1 vm2 :
  Sv.Subset s1 s2 -> vm1 = vm2 [\s1] -> vm1 = vm2 [\s2].
Proof. by move=> le_12 heq x xin; apply: heq; SvD.fsetdec. Qed.

Lemma svmap_eq_except_sym vm1 vm2 s :
  vm1 = vm2 [\s] -> vm2 = vm1 [\s].
Proof. by move=> heq x xin; rewrite heq. Qed.

Global Instance equiv_svmap_eq_except s : Equivalence (svmap_eq_except s).
Proof. constructor=> //.
+ by move=> ??; apply: svmap_eq_except_sym.
+ by move=> ???; apply: svmap_eq_except_trans.
Qed.

Global Instance svmap_eq_except_impl :
  Proper (Sv.Subset ==> eq ==> eq ==> Basics.impl) svmap_eq_except.
Proof.
by move=> s1 s2 h vm1 ? <- vm2 ? <-; apply: svmap_eq_except_subset.
Qed.

Global Instance svmap_eq_except_m :
  Proper (Sv.Equal ==> eq ==> eq ==> iff) svmap_eq_except.
Proof.
move=> s1 s2 heq vm1 ? <- vm2 ? <-; split;
  by apply: svmap_eq_except_subset; rewrite heq.
Qed.

Lemma svmap_eq_exceptL vm1 vm2 s1 s2 :
  vm1 = vm2 [\s1] -> vm1 = vm2 [\Sv.union s1 s2].
Proof. by apply/svmap_eq_except_subset/SvP.MP.union_subset_1. Qed.

Lemma svmap_eq_exceptR vm1 vm2 s1 s2 :
  vm1 = vm2 [\s2] -> vm1 = vm2 [\Sv.union s1 s2].
Proof. by apply/svmap_eq_except_subset/SvP.MP.union_subset_2. Qed.

(* -------------------------------------------------------------------- *)
(*Lemma swrite_var_eqmem vi v s s' :
  swrite_var vi v s = ok s' -> sevm s = sevm s' [\Sv.singleton vi].
Proof.
apply: rbindP => sv /=; apply: on_vuP.
move=> z _ <- h; apply ok_inj in h; subst s'.
move=> x hx; rewrite Fv.setP_neq //; apply/negP => /eqP.
by SvD.fsetdec.
move=> h; case eqP => // ne k; apply ok_inj in k; subst.
move=> k; apply ok_inj in k; subst.
reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
Lemma swrite_sget_var i z s s' :
  swrite_var i z s = ok s' -> sget_var s'.(sevm) i = z.
Proof.
elim/rbindP=> si; elim/on_vuP.
move => y h <- x; apply ok_inj in x; subst.
rewrite /sget_var Fv.setP_eq; move: (_ (vtype _)) y h.
move=> sst y h; apply: (@of_sval_inj sst).
+ by apply/sval_sstype_to_sval.
+ by apply: (sval_sstype_of_sval h).
+ by rewrite of_sval_to_sval h.
move => h; case: eqP => // ne k; apply ok_inj in k; subst.
move=> k; apply ok_inj in k; subst.
Abort.

(* -------------------------------------------------------------------- *)
Lemma vrvP gd r v s s' :
  swrite_lval gd r v s = ok s' -> s.(sevm) = s'.(sevm) [\ vrv r].
Proof. case: r => /=.
+ by move=> _ _ [->].
+ by move=> vi /swrite_var_eqmem; rewrite SvP.MP.singleton_equal_add.
+ by move=> vi e; t_xrbindP => *; subst.
+ move=> vi pe /slet_inv[p [eq]]; t_xrbindP=> z v' /=.
  move=> okv' okz w okw sv; apply: on_vuP.
  - move => /= e h <- <- /=.
  rewrite -SvP.MP.singleton_equal_add => x inx.
  by rewrite Fv.setP_neq //; apply/eqP; SvD.fsetdec.
  - move=> h; case: eqP => // ne k ?; apply ok_inj in k; subst.
    reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
Lemma vrvsP gd rs vs s s' : swrite_lvals gd s rs vs = ok s' ->
  s.(sevm) = s'.(sevm) [\ vrvs rs].
Proof.
elim: rs vs s => [|r rs ih] [|v vs] s //= => [[->]//|].
elim/rbindP=> si /vrvP h1 {ih}/ih h2; rewrite vrvs_cons.
by transitivity (sevm si);
  [apply: svmap_eq_exceptL | apply: svmap_eq_exceptR].
Qed.

(* -------------------------------------------------------------------- *)
Lemma writeP p gd c s1 s2 :
  ssem p gd s1 c s2 -> s1.(sevm) = s2.(sevm) [\ write_c c].
Proof.
eapply (@ssem_Ind p gd
  (fun s1 c s2 => sevm s1 = sevm s2 [\write_c c])
  (fun s1 i s2 => sevm s1 = sevm s2 [\write_i i])
  (fun s1 i s2 => sevm s1 = sevm s2 [\write_I i])
  (fun x sz s1 c s2 => sevm s1 = sevm s2 [\Sv.add x (write_c c)])
  (fun _ _ _ _ _ => True)) => // {s1 s2 c}.
+ move=> s1 s2 s3 i c _ hi _ hc; writeN; transitivity (sevm s2).
  by apply: svmap_eq_exceptL. by apply: svmap_eq_exceptR.
+ by move=> s1 s2 x tg e; t_xrbindP=> z _ /vrvP h; writeN.
+ by move=> s1 s2 t o xs es; t_xrbindP=> vs vs'; writeN=> _ _ /vrvsP.
+ by move=> s1 s2 e c1 c2 _ _; writeN; apply/svmap_eq_exceptL.
+ by move=> s1 s2 e c1 c2 _ _; writeN; apply/svmap_eq_exceptR.
+ move=> s1 s2 s3 s4 c e c'; writeN=> _ h1 _ _ h2 _ h3; transitivity (sevm s3) =>//.
  by transitivity (sevm s2); [apply: svmap_eq_exceptL | apply: svmap_eq_exceptR].
+ by move=> s1 s2 c e c'; writeN=> _ h1 _; apply: svmap_eq_exceptL.
+ move=> s1 s2 x d lo hi c vlo vhi; writeN=> _ _ h.
  by rewrite SvP.MP.add_union_singleton.
+ move=> s1 s1' s2 s3 x w ws c /swrite_var_eqmem h1 _ h2 _ h3.
  transitivity (sevm s2) => //; rewrite SvP.MP.add_union_singleton.
  by transitivity (sevm s1'); [apply: svmap_eq_exceptL | apply: svmap_eq_exceptR].
+ by move=> s1 m s2 ii xs fn args vargs vs okv _ _ /vrvsP /=; writeN.
Qed.*)
