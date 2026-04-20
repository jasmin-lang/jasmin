Require Import Paco.paco.
From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms.
From ITree Require Import
     ITree ITreeFacts     
     Basics.Utils
     Basics.Category
     Basics.Basics
     Basics.Function
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion
     Interp.RecursionFacts
     Events.Exception.
Import ITreeNotations.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Require Import while it_exec it_exec_sem.

Lemma while_join_split {E} `{ErrEvent -< E} {err: error_data} {I}
  (cond1 cond2 : I -> bool) (DC: forall x, cond1 x -> cond2 x -> False)
  (step : I -> itree E I) (i0: I) : 
  let cond12 := fun x => cond1 x || cond2 x in
  eutt eq (while cond12 step i0)
          (while cond12 (fun i1 => if cond1 i1
                            then while cond1 step i1
                            else if cond2 i1
                                 then while cond2 step i1
                                 else throw err) i0).
Proof.
  assert (forall x, cond1 x \/ cond2 x 
                    \/ ((cond1 x = false) /\ (cond2 x = false))) as IV.
  { intros i1.
    destruct (cond1 i1); eauto.
    destruct (cond2 i1); eauto. }
  unfold while, while_body; simpl.
  revert i0.
  ginit. gcofix CIH.
  intro i0.
  setoid_rewrite unfold_iter.
  destruct (cond1 i0 || cond2 i0) eqn: was_e1; simpl.
  2: { setoid_rewrite bind_ret_l; simpl.
       gstep; red. econstructor; auto. }
  setoid_rewrite bind_bind.
  setoid_rewrite bind_ret_l; simpl.
  destruct (cond1 i0) eqn: was_e2; simpl.
  { (* cond1 i0 *)
    setoid_rewrite unfold_iter at 2.
    setoid_rewrite bind_bind.
    rewrite was_e2; simpl.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l; simpl.

    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); try reflexivity.
    clear was_e1 was_e2. clear i0.

    intros i2 i1 hh.
    inversion hh; subst. clear H0.
    setoid_rewrite bind_tau.
    specialize (IV i1).
    destruct IV as [IV | [IV | [IV1 IV2]]].
    {  (* cond1 i1 *)
      gstep; red; econstructor.
      set (T0 := ITree.iter _ _).
      set (K0 := ITree.iter _).
      set (K1 := ITree.iter _).
      assert (eq_itree eq (r0 <- K0 i1;; Tau (K1 r0))%itree (K1 i1)) as A1.
      { subst K0 K1.
        setoid_rewrite unfold_iter at 5.
        rewrite IV; simpl.
        setoid_rewrite bind_bind.
        setoid_rewrite bind_ret_l; simpl; reflexivity.
      }  
      rewrite A1; eauto.
      gfinal; left. eapply CIH.
    }  
    { (* cond2 i1 *)
      setoid_rewrite unfold_iter at 2.
      setoid_rewrite bind_bind.
      assert (cond1 i1 = false) as A1.
      { destruct (cond1 i1) eqn: e1; auto.
        specialize (DC _ e1 IV); intuition.
      }
      rewrite A1; simpl.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite tau_euttge at 2.
      gstep; red; econstructor.
      gfinal; left. eapply CIH.
    }  
    { setoid_rewrite tau_euttge.
      setoid_rewrite unfold_iter.
      setoid_rewrite bind_bind.
      rewrite IV1; simpl.
      rewrite IV2; simpl.
      setoid_rewrite bind_ret_l.
      setoid_rewrite bind_ret_l.
      rewrite IV1; simpl.
      rewrite IV2; simpl.
      setoid_rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      gstep; red. econstructor; auto.
    }
  }
  { (* cond2 i0 *)
    assert (cond2 i0 = true) as A1. 
    { destruct (cond2 i0); auto. }
    rewrite A1; simpl.
    setoid_rewrite unfold_iter at 2.
    setoid_rewrite bind_bind.
    rewrite A1; simpl.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l; simpl.

    guclo eqit_clo_bind.
    econstructor 1 with (RU := eq); try reflexivity.
    clear was_e1 was_e2 A1. clear i0.

    intros i2 i1 hh.
    inversion hh; subst. clear H0.
    setoid_rewrite bind_tau.
    specialize (IV i1).
    destruct IV as [IV | [IV | [IV1 IV2]]].
    {  (* cond1 i1 *)
      setoid_rewrite unfold_iter at 2.
      setoid_rewrite bind_bind.
      assert (cond2 i1 = false) as A1.
      { destruct (cond2 i1) eqn: e1; auto.
        specialize (DC _ IV e1); intuition.
      }
      rewrite A1; simpl.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite tau_euttge at 2.
      gstep; red; econstructor.
      gfinal; left. eapply CIH.
    }
    {  (* cond2 i1 *)
      gstep; red; econstructor.
      set (T0 := ITree.iter _ _).
      set (K0 := ITree.iter _).
      set (K1 := ITree.iter _).
      assert (eq_itree eq (r0 <- K0 i1;; Tau (K1 r0))%itree (K1 i1)) as A1.
      { subst K0 K1.
        setoid_rewrite unfold_iter at 5.
        rewrite IV; simpl.
        assert (cond1 i1 = false) as A2.
        { destruct (cond1 i1) eqn: e1; auto.
          specialize (DC _ e1 IV); intuition.
        }
        rewrite A2; simpl.
        setoid_rewrite bind_bind.
        setoid_rewrite bind_ret_l; simpl. reflexivity.
      } 
      rewrite A1; eauto.
      gfinal; left. eapply CIH.
    }
    { setoid_rewrite tau_euttge.
      setoid_rewrite unfold_iter.
      setoid_rewrite bind_bind.
      rewrite IV1; simpl.
      rewrite IV2; simpl.
      setoid_rewrite bind_ret_l.
      setoid_rewrite bind_ret_l.
      rewrite IV1; simpl.
      rewrite IV2; simpl.
      setoid_rewrite bind_ret_l.
      setoid_rewrite tau_euttge.
      gstep; red. econstructor; auto.
    }
  }
Qed.    

Lemma while_join_triv {E} `{ErrEvent -< E} {err: error_data} {I}
  (cond1 cond2 : I -> bool) (step : I -> itree E I) (i0: I) : 
  let cond12 := fun x => cond1 x || cond2 x in
  eutt eq (while cond12 step i0)
          (while cond12 (fun i1 => if cond1 i1
                            then step i1
                            else if cond2 i1
                                 then step i1
                                 else throw err) i0).
Proof.
  unfold while, while_body; simpl.
  eapply eutt_iter; intros i1.
  destruct (cond1 i1 || cond2 i1) eqn:was_e0; simpl; try reflexivity.
  destruct (cond1 i1) eqn:was_e1; simpl; try reflexivity.
  destruct (cond2 i1) eqn:was_e2; simpl; try reflexivity.
  intuition auto with *.
Qed.  
  
Lemma while_join_lemma {E} `{ErrEvent -< E} {err: error_data} {I}
  (cond1 cond2 : I -> bool) (DC: forall x, cond1 x -> cond2 x -> False)
  (step : I -> itree E I) (i0: I) : 
  let cond12 := fun x => cond1 x || cond2 x in
  eutt eq (while cond12 (fun i1 => if cond1 i1
                            then step i1
                            else if cond2 i1
                                 then step i1
                                 else throw err) i0)
          (while cond12 (fun i1 => if cond1 i1
                            then while cond1 step i1
                            else if cond2 i1
                                 then while cond2 step i1
                                 else throw err) i0).
Proof.
  simpl; rewrite <- while_join_triv.  
  rewrite while_join_split; auto.
  reflexivity.
Qed.  
  
