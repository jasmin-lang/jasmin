(** Relation with trace. *)

From Coq Require Import Utf8 Relation_Definitions Relation_Operators.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TRACE_CLOSURE.
  Context {A D T: Type} {R: A → D → A → T → Prop}.

  Fixpoint trace_closure_rec (α: A) (d: seq D) (ω: A) (tr: seq T) :=
    match d, tr with
    | [::], [::] =>  α = ω
    | d::d', t::tr' => exists2 β, R α d β t & trace_closure_rec β d' ω tr'
    | _, _ => False
    end.

  Definition trace_closure := nosimpl trace_closure_rec.

  Lemma tc_refl α : trace_closure α [::] α [::].
  Proof. done. Qed.

  Lemma tc_step α d t β :
    R α d β t →
    trace_closure α [::d] β [::t].
  Proof. by exists β. Qed.

  Lemma tc_trans β α dr tr dr' tr' ω :
    trace_closure α dr β tr →
    trace_closure β dr' ω tr' →
    trace_closure α (dr ++ dr') ω (tr ++ tr').
  Proof.
    rewrite /trace_closure; elim: dr tr α => /=.
    + by move=> [] //= α -> /=.
    move=> d dr t [] //= a l α [α' h htr htr'].
    by exists α'; auto.
  Qed.

  Lemma tc_left α d t β dr tr ω :
    R α d β t →
    trace_closure β dr ω tr →
    trace_closure α (d :: dr) ω (t :: tr).
  Proof. by move=> HR Htr; exists β. Qed.

  Lemma tc_right ψ α dr tr d t ω :
    trace_closure α dr ψ tr →
    R ψ d ω t →
    trace_closure α (rcons dr d) ω (rcons tr t).
  Proof. by rewrite -cats1 -cats1 => H1 /tc_step;apply: tc_trans. Qed.

  Lemma tc_nil {α ω} : trace_closure α [::] ω [::] -> α = ω.
  Proof. done. Qed.

  Lemma tc_cons {α d t dr tr ω} :
    trace_closure α (d :: dr) ω (t :: tr) ->
    exists2 β, R α d β t & trace_closure β dr ω tr.
  Proof. done. Qed.

End TRACE_CLOSURE.

Arguments trace_closure [_ _] _ _ _ _.
