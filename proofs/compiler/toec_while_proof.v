From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg word_ssrZ.
Require Import compiler_util pseudo_operator psem psem_facts.
Require Import toec_while.
Import Utf8.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withassert.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : prog) (ev:extra_val_t).
Definition p' := toec_while_prog p.

(* ------------------------------------------------- *)

Let Pi (i : instr) :=
   forall c', toec_while_i i = c'
              -> wequiv_rec p' p ev ev eq_spec eq c' [:: i] eq.

Let Pi_r (i:instr_r) := forall ii, Pi (MkI ii i).

Let Pc  (c:cmd) :=
   forall c', toec_while_c toec_while_i c = c'
              -> wequiv_rec p' p ev ev eq_spec eq c' c eq.

Lemma ec_while_sem_pre fn fsi fs :
  fsi = fs →
  sem_pre p' fn fsi = ok tt → sem_pre p fn fs = ok tt.
Proof.
  rewrite /sem_pre /p' => - ->.
  rewrite get_map_prog_name.
  by case: get_fundef.
Qed.

Lemma ec_while_sem_post fr1 fr2 fs fsi fn:
  fr1 = fr2
  → fvals fsi = fvals fs
  → sem_post p' fn (fvals fsi) fr1 = ok tt → sem_post p fn (fvals fs) fr2 = ok tt.
Proof.
  rewrite /sem_post /p' => -> ->.
  rewrite get_map_prog_name.
  by case: get_fundef.
Qed.

Lemma ec_while_l fn : wiequiv_f p' p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply wequiv_fun_ind_wa =>{} fn fn' fsi fs.
  move => [<- hrel] fdi.
  rewrite get_map_prog_name.
  case: get_fundef => [fd | //] [= hcomp].
  exists fd => // hsem.
  split; first by apply (ec_while_sem_pre hrel).
  move=> si hinit.
  exists si.
  { by subst. }
  exists eq, eq.
  split; first done; first last.
  { move : hrel => -> fr1 fr2 ->.
    by apply ec_while_sem_post.
  }
  { move=> i1 i2 o1 <- //= H. subst. by exists o1. }

  clear -Pc Pi Pi_r hcomp hsem.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)).
  { done. }
  { rewrite /Pc /toec_while_c /= => c <-. by apply wequiv_nil. }
  { move=> i c Hi Hc ? /= <-.
    rewrite -cat1s. eapply wequiv_cat. by apply Hi. by apply Hc.
  }
  { move=> x tg ty e ii i <-. apply wequiv_assgn_eq.
    by apply wrequiv_eq. intro. by apply wrequiv_eq.
  }
  { move=> xs t o es ii i <-. apply wequiv_opn_eq.
    by apply wrequiv_eq. intro. by apply wrequiv_eq.
  }
  { move=> xs o es ii i <-. apply wequiv_syscall_eq. by move=>??->.
    by apply wrequiv_eq. intro. by apply wrequiv_eq.
    intro. by apply wrequiv_eq.
  }
  { move=> a ii i <-. apply wequiv_assert_eq. split; first done.
    by apply wrequiv_eq. done.
  }
  { move=> e c1 c2 Hc1 Hc2 ii i <-. apply wequiv_if_eq.
    by apply wrequiv_eq. case. by apply Hc1. by apply Hc2.
  }
  { move=> v dir lo hi c Hc ii i <-. eapply wequiv_for_eq.
    done. by apply wrequiv_eq. intro. by apply wrequiv_eq.
    by apply Hc.
  }
  { move=> a cdo e info cwh Hcdo Hcwh ii cf <-.
    rewrite /wequiv_rec /wequiv /wkequiv /wkequiv_io.
    setoid_rewrite isem_cmd_while_rotate.
    change (wequiv_rec p' p ev ev eq_spec eq
              (toec_while_i (MkI ii (Cwhile a cdo e info cwh)))
              (cdo ++ [:: MkI ii (Cwhile a [::] e info (cwh ++ cdo))])
              eq).
    apply (wequiv_cat (Hcdo _ erefl)).
    apply wequiv_while.
    + by move=>s1 s2 b <- ->; eexists.
    + by apply wequiv_nil.
    + exact (wequiv_cat (Hcwh _ erefl) (Hcdo _ erefl)).
  }
  { move=> xs f es ii i <- /=.
    eapply wequiv_call_wa
      with (Pf:=rpreF (eS:=eq_spec)) (Qf:= rpostF (eS:=eq_spec)).
    - by apply wrequiv_eq.
    - move=> s1 s2 vs1 vs2 <- <-. by apply ec_while_sem_pre.
    - by intros; subst.
    - move=> fs1 fs2 fr1 fr2  [_ ->] ->.
      exact (ec_while_sem_post erefl erefl).
    - move=>???. by apply wequiv_fun_rec.
    - move=>fs1 fs2 fr1 fr2 [_ ->] ->.
      by apply wrequiv_eq.
  }
  { by rewrite -hcomp. }
Qed.

End PROOF.

