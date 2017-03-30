Require dmasm_Ssem.

Require Import Utf8.
Import Morphisms.
Import ssreflect.
Import ssrbool.
Import eqtype.
Import seq.
Import ZArith.
Local Open Scope Z_scope.

Import dmasm_utils.
Import dmasm_type.
Import dmasm_var.
Import dmasm_expr.
Import dmasm_sem.
Import dmasm_Ssem.
Import memory.
Import UnsafeMemory.

Lemma ssem_inv { prg s c s' } :
  ssem prg s c s' →
  match c with
  | [::] => s' = s
  | i :: c' => ∃ si, ssem_I prg s i si ∧ ssem prg si c' s'
end.
Proof. case; eauto. Qed.

Lemma ssem_I_inv { prg s i s' } :
  ssem_I prg s i s' →
  ∃ i' ii, i = MkI ii i' ∧ ssem_i prg s i' s'.
Proof. case; eauto. Qed.

Lemma ssem_i_inv { prg s i s' } :
  ssem_i prg s i s' →
  match i with
  | Cassgn x tg e => ∃ v, ssem_pexpr s e = ok v ∧ swrite_rval x v s = ok s'
  | _ => True
  end.
Proof.
  case; eauto.
  clear.
  move=> s s' x _ e H. case: (bindW H). eauto.
Qed.

Definition MkI_inj {ii i ii' i'} (H: MkI ii i = MkI ii' i') :
  ii = ii' ∧ i = i' :=
  let 'Logic.eq_refl := H in conj Logic.eq_refl Logic.eq_refl.

Definition hpred : Type :=
  sestate → Prop.

Notation "A ⊂ B" := (∀ x, A x → B x) (at level 80) : msem_scope.

Local Open Scope msem_scope.

Section HOARE_LOGIC.

Context (prg: prog).

Definition hoare (Pre: hpred) (c: cmd) (Post: hpred) : Prop :=
  ∀ s s' : sestate,
    ssem prg s c s' →
    Pre s → Post s'.

Lemma hoare_conseq (P1 Q1: hpred) (c: cmd) (P2 Q2: hpred) :
  P2 ⊂ P1 → Q1 ⊂ Q2 →
  hoare P1 c Q1 → hoare P2 c Q2.
Proof. firstorder. Qed.

Lemma hoare_skip_core P : hoare P [::] P.
Proof. by move => s s' H; case (ssem_inv H). Qed.

Lemma hoare_skip (Q P: hpred) : Q ⊂ P → hoare Q [::] P.
Proof. eauto using hoare_conseq, hoare_skip_core. Qed.

Lemma hoare_cons R P Q i c :
  hoare P [:: i] R →  hoare R c Q →  hoare P (i :: c) Q.
Proof.
  by
  move=> Hi Hc s s' /ssem_inv [ s1 [Hi' Hc']] H;
  eauto using SEseq, SEskip.
Qed.

Lemma hoare_assgn (P: hpred) ii x tag e :
  hoare
    (λ s, ∀ v s',
        ssem_pexpr s e = ok v →
        swrite_rval x v s = ok s' →
        P s')
    [:: MkI ii (Cassgn x tag e) ] P.
Proof.
  move=> s s1 / ssem_inv [ s' [Hi /ssem_inv]] ->.
  case: (ssem_I_inv Hi) => i' [ ii' [ /MkI_inj [? ?] Hi' ] ]; clear Hi; subst ii' i'.
  move: (ssem_i_inv Hi') => [ v [ Hv Hs' ] ].
  exact (λ H, H _ _ Hv Hs').
Qed.

End HOARE_LOGIC.

Section WEAKEST_PRECONDITION.

(* A formula is a predicate over an environment that maps logical variables to value. *)
(* This predicate should be extensional *)

Definition env : Type := Mv.t ssem_t.
Definition env_ext (m m': env) : Prop :=
  ∀ x, (m.[x] = m'.[x])%mv.

Definition env_ext_refl m : env_ext m m := λ x, Logic.eq_refl.

Definition env_ext_sym m m' (H: env_ext m m') : env_ext m' m :=
  λ x, Logic.eq_sym (H x).

Definition env_ext_trans m' m m'' (H: env_ext m m') (H': env_ext m' m'') :
  env_ext m m'' :=
  λ x, Logic.eq_trans (H x) (H' x).

Lemma env_ext_empty m m' :
  (∀ x, m x = m' x) →
  env_ext (Mv.empty m) (Mv.empty m').
Proof. by move=> E x; rewrite ! Mv.get0. Qed.

Lemma env_ext_set m m' x v :
  env_ext m m' →
  (env_ext (m.[x <- v]) (m'.[x <- v]))%mv.
Proof.
  move=> E y.
  case: (x =P y) => [ <- | H ].
  rewrite ! Mv.setP_eq //.
  assert (x != y) by (case: eqP => //).
  rewrite ! Mv.setP_neq //.
Qed.

Definition formula : Type :=
  sigT (Proper (@eq mem ==> env_ext ==> iff)).

Lemma formula_m (f: mem → env → Prop) :
  (∀ m s s', env_ext s s' → f m s → f m s') →
  Proper (@eq mem ==> env_ext ==> iff) f.
Proof.
  move=> E m ? <- s s' H.
  split; eauto using env_ext_sym.
Qed.

Instance constant_formula_m (P: Prop) : Proper (@eq mem ==> env_ext ==> iff) (λ _ _, P) :=
  formula_m _ (λ _ _ _ _ (p: P), p).

Example ftrue: formula := existT _ (λ _ _, True) _.
Example ffalse: formula := existT _ (λ _ _, False) _.

Definition formula_of_hpred (P: hpred) : formula.
Proof.
  refine (existT _ (λ (m: mem) (s: env), P {| semem := m ; sevm := Fv.empty (λ x, s.[x])%mv |}) _).
  apply formula_m.
  move=> m s s' E H.
  refine (eq_ind _ P H _ _).
  f_equal.
  apply Fv.map_ext. auto.
Defined.

Notation "⟨ P ⟩" := (formula_of_hpred P) : msem_scope.

Definition formula_denote (f: formula) : hpred :=
  λ s, projT1 f (semem s) (Mv.empty (λ x, (sevm s).[x])%vmap).

Notation "⟦ f ⟧" := (formula_denote f) : msem_scope.

Lemma formula_of_hpred_denote P :
  ∀ s, ⟦ ⟨P⟩ ⟧ s ↔ P s.
Proof.
  unfold formula_of_hpred, formula_denote. simpl.
  by
  move=> [ m vm ]; split; move=> H; refine (eq_ind _ P H _ _); f_equal; apply Fv.map_ext; move=> x;
  rewrite Fv.get0 Mv.get0.
Qed.

Remark ffalse_denote (P: Prop) s : ⟦ ffalse ⟧ s → P.
Proof. easy. Qed.

End WEAKEST_PRECONDITION.
