(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.

Require Import Morphisms ZArith.

Require Import utils type var.
Require Import expr sem Ssem Ssem_props wp.
Require Import memory.
Require Import Psatz.

Import UnsafeMemory.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Local Open Scope Z_scope.
Local Open Scope svmap_scope.

(* -------------------------------------------------------------------- *)
Hint Resolve 0 SEskip.
Hint Resolve SEseq : ssem.

Notation strue  := (SVbool true).
Notation sfalse := (SVbool false).

(* -------------------------------------------------------------------- *)
Inductive dupI (P : Prop) := Dup of P & P.

Lemma dup (P : Prop) : P -> dupI P.
Proof. by move=> hP; constructor. Qed.

(* -------------------------------------------------------------------- *)
Notation e2b s e := (eval_texpr s (texpr_of_pexpr sbool' e)).

(* -------------------------------------------------------------------- *)
Lemma ssem_app_inv prg s c1 c2 s' :
  ssem prg s (c1 ++ c2) s' ->
    exists2 si : sestate, ssem prg s c1 si & ssem prg si c2 s'.
Proof.
elim: c1 s => /= [|i c1 ih] s c; first by exists s.
by case/ssem_inv: c => si [?] /ih []; eauto with ssem.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ssem_inv1_r prg s i s' : ssem prg s [:: i] s' -> ssem_I prg s i s'.
Proof. by case/ssem_inv=> si [? /ssem_inv ->]. Qed.

(* -------------------------------------------------------------------- *)
Lemma ssem_inv1 prg z s i s' : ssem prg s [:: MkI z i] s' -> ssem_i prg s i s'.
Proof. by case/ssem_inv1_r/ssem_I_inv=> [ir] [ii] [] [_ ->]. Qed.

(* -------------------------------------------------------------------- *)
Lemma hoare_seq prg R P Q c1 c2 :
  hoare prg P c1 R -> hoare prg R c2 Q -> hoare prg P (c1 ++ c2) Q.
Proof. by move=> h1 h2 s s' /ssem_app_inv[si hc1 hc2]; eauto. Qed.

(* -------------------------------------------------------------------- *)
Lemma hoare_rcons prg R P Q c i :
  hoare prg P c R -> hoare prg R [:: i] Q -> hoare prg P (rcons c i) Q.
Proof. by move=> h1 h2; rewrite -cats1; apply: (@hoare_seq _ R). Qed.

(* -------------------------------------------------------------------- *)
Lemma hoare_while prg z I e c :
   hoare prg (fun s => I s /\ e2b s e) c I
-> hoare prg I [:: MkI z (Cwhile e c)]
         (fun s => I s /\ ~~ e2b s e).
Proof.
move=> h s s' /ssem_inv1; move: {-2}(Cwhile _ _) (erefl (Cwhile e c)).
move=> ir eq C; elim: C eq => // {s}; last first.
+ move=> s e' c' hlet [<- _] Is; split=> //.
  elim/rbindP: hlet => v he' /sto_bool_inv hv; subst v.
  by move: he' => /texpr_of_pexpr_bool ->.
move=> s1 s2 s3 e' c' hlet hc' _ ih [eqe eqc] Is1; subst e' c'.
apply/ih/(h s1) => //; split=> //; elim/rbindP: hlet.
move=> v he' /sto_bool_inv ?; subst v.
by move: he' => /texpr_of_pexpr_bool ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma hoare_while_seq prg z P I c0 e c :
   hoare prg P c0 I
-> hoare prg (fun s => I s /\ e2b s e) c I
-> hoare prg P (rcons c0 (MkI z (Cwhile e c)))
         (fun s => I s /\ ~~ e2b s e).
Proof. by move=> h0 h; apply: (hoare_rcons h0); apply: hoare_while. Qed.

(* -------------------------------------------------------------------- *)
Definition hoare_for prg x zs P c Q :=
  forall s s', ssem_for prg x zs s c s' -> P s -> Q s'.

Local Notation "s `_ n" := (nth 0 s n).

Lemma hoare_genfor prg (x : var) z0 zs (P : Z -> sestate -> Prop) c :
   (forall s1 s2 z, s1.(sevm) = s2.(sevm) [\ Sv.singleton x] ->
      P z s1 -> P z s2)
-> (forall n, (n < size zs)%nat ->
      hoare prg
        (fun s => P (z0 :: zs)`_n s /\ sget_var s.(sevm) x = SVint zs`_n)
        c (P (z0 :: zs)`_n.+1))
-> hoare_for prg x zs (P z0) c (P (last z0 zs)).
Proof.
move=> eqs h s s' C; elim: zs z0 s h C => [|z zs ih] z0 s /= h.
+ by elim/sfor_nilI.
move=> C; elim/sfor_consI: C eqs ih h => {x}.
move=> s1' s2 i oks1' h1 h2 eqs ih h Ps.
have {Ps} Ps2: P z s2; first apply: (h 0%nat _ s1') => //=.
+ rewrite (swrite_sget_var oks1'); split=> //.
  by apply: (eqs s) => //; apply/swrite_var_eqmem/oks1'.
by apply: (ih _ s2) => //= n ltnsz; apply/(h n.+1).
Qed.

(* -------------------------------------------------------------------- *)
Lemma hoare_for_to
   prg z (x : var_i) lo hi vlo vhi (P : Z -> sestate -> Prop) c
:  vlo < vhi
->  (forall s1 s2 z, s1.(sevm) = s2.(sevm) [\ Sv.singleton x] ->
      P z s1 -> P z s2)
-> (forall i, vlo <= i < vhi ->
      hoare prg
        (fun s => P (i-1) s /\ sget_var s.(sevm) x = i) c (P i))
-> hoare prg
     (fun s => [/\ P (vlo-1) s
        , eval_texpr s (texpr_of_pexpr sint' lo) = vlo
        & eval_texpr s (texpr_of_pexpr sint' hi) = vhi])
     [:: MkI z (Cfor x (UpTo, lo, hi) c)]
     (P (vhi-1)).
Proof.
move=> lt eqs h s1 s2 /ssem_inv1 sh [hP eqlo eqhi].
pose s := wrange UpTo vlo vhi; rewrite -(last_wrange_up_ne (vlo-1) lt).
apply: (@hoare_genfor prg x (vlo-1) (wrange UpTo vlo vhi) P c);
  try eassumption; last first.
+ sinversion sh; move: H6 H7; t_xrbindP.
  move=> slo hlo /sto_int_inv ? shi hhi /sto_int_inv ?; subst.
  move/texpr_of_pexpr_int: hhi => ->.
  by move/texpr_of_pexpr_int: hlo => ->.
rewrite size_wrange wrange_cons // => n lt_n_sz s'1 s'2.
rewrite !nth_wrange //; try apply/leP/Nat2Z.inj_le.
+ by move/leP/Nat2Z.inj_le: lt_n_sz; rewrite !Z2Nat.id; lia.
+ by move/leP/Nat2Z.inj_le: lt_n_sz; rewrite !Z2Nat.id; lia.
rewrite [_+Z.of_nat _.+1](_ : _ = vlo + Z.of_nat n); first lia.
rewrite [_-1+_](_ : _ = vlo + Z.of_nat n- 1); first lia.
apply: h; move/leP/Nat2Z.inj_le: lt_n_sz; rewrite Z2Nat.id; lia.
Qed.
