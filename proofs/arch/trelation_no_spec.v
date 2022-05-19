(** Relation with trace. *)

From Coq Require Import Utf8 Relation_Definitions Relation_Operators.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TRACE_CLOSURE.
  Context {A T: Type} {R: A → T → A → Prop}.

  Fixpoint trace_closure_rec (α: A) (tr: seq T) (ω: A) :=
    match tr with
    | [::] =>  α = ω
    | t::tr' => exists2 β, R α t β & trace_closure_rec β tr' ω
    end.

  Definition trace_closure := nosimpl trace_closure_rec.

  Lemma tc_refl α : trace_closure α [::] α.
  Proof. done. Qed.

  Lemma tc_step α t β :
    R α t β →
    trace_closure α [::t] β.
  Proof. by exists β. Qed.

  Lemma tc_trans β α tr tr' ω :
    trace_closure α tr β →
    trace_closure β tr' ω →
    trace_closure α (tr ++ tr') ω.
  Proof.
    rewrite /trace_closure; elim: tr α => /= [ | t tr Hrec] α; first by move => ->.
    by case => γ HR Htr /(Hrec _ Htr); exists γ.
  Qed.

  Lemma tc_left α t β tr ω :
    R α t β →
    trace_closure β tr ω →
    trace_closure α (t :: tr) ω.
  Proof. by move=> HR Htr; exists β. Qed.

  Lemma tc_right ψ α tr t ω :
    trace_closure α tr ψ →
    R ψ t ω →
    trace_closure α (rcons tr t) ω.
  Proof. by rewrite -cats1 => H1 /tc_step; apply: tc_trans. Qed.

  Lemma tc_nil {α ω} : trace_closure α [::] ω -> α = ω.
  Proof. done. Qed.

  Lemma tc_cons {α t tr ω} :
    trace_closure α (t :: tr) ω ->
    exists2 β, R α t β & trace_closure β tr ω.
  Proof. done. Qed.

  Lemma tc_cons1 {α t ω} : trace_closure α [::t] ω -> R α t ω.
  Proof. by case=> β Hr /tc_nil <-. Qed.

  Lemma tc_cat {α tr tr' ω} :
    trace_closure α (tr ++ tr') ω ->
    exists2 β, trace_closure α tr β & trace_closure β tr' ω.
  Proof.
    rewrite /trace_closure;elim: tr α => /= [ | t tr Hrec] α.
    + by exists α.
    by case=> β HR /Hrec [β' ??]; exists β' => //; exists β.
  Qed.

  Lemma tc_rcons {α tr t ω} :
    trace_closure α (rcons tr t) ω ->
    exists2 β, trace_closure α tr β & R β t ω.
  Proof.
    by rewrite -cats1 => /tc_cat [β ? /tc_cons1 ?]; exists β.
  Qed.

  Lemma erase_trace (R': relation A) :
    (∀ α t ω, R α t ω → R' α ω) →
    ∀ α tr ω,
    trace_closure α tr ω →
    clos_refl_trans _ R' α ω.
  Proof.
    move=> hr α tr;elim: tr α => [ | t tr Hrec] α ω.
    + by move=> /tc_nil <-;apply rt_refl.
    case/tc_cons => β HR /Hrec; apply: rt_trans;apply: rt_step;apply: hr HR.
  Qed.

End TRACE_CLOSURE.

Arguments trace_closure [_ _] _ _ _ _.
