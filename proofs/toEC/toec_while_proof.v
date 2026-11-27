From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg word_ssrZ.
Require Import compiler_util pseudo_operator psem psem_facts.
Require Import toec_while.
Import Utf8.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {wa : WithAssert}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : prog) (ev:extra_val_t).
Definition p' := toec_while_prog p.

(* ------------------------------------------------- *)

Let Pi (i : instr) :=
      forall env c', toec_while_i i = c'
                 -> wequiv_rec (env1:=env) (env2:=env) p' p ev ev eq_spec eq c' [:: i] eq.

Let Pi_r (i:instr_r) := forall ii, Pi (MkI ii i).

Let Pc  (c:cmd) :=
      forall env c', toec_while_c toec_while_i c = c'
                 -> wequiv_rec (env1:=env) (env2:=env) p' p ev ev eq_spec eq c' c eq.

Lemma ec_while_sem_pre fn vals fsi fs :
  fsi = fs →
  sem_pre p' fn vals fsi = ok tt → sem_pre p fn vals fs = ok tt.
Proof.
  rewrite/sem_pre/p' => - ->.
  rewrite get_map_prog_name.
  by case: get_fundef.
Qed.

Lemma ec_while_sem_post fr1 fr2 fs fsi fn vals:
  fr1 = fr2
  → fvals fsi = fvals fs
  → sem_post p' fn vals (fvals fsi) fr1 = ok tt → sem_post p fn vals (fvals fs) fr2 = ok tt.
Proof.
  rewrite /sem_post /p' => -> ->.
  rewrite get_map_prog_name.
  by case: get_fundef.
Qed.

#[local] Hint Resolve wrequiv_eq : core.

Lemma toec_while_l fn : wiequiv_f p' p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply wequiv_fun_ind_wa =>{} fn fn' vals vals' fsi fs.
  move => [<- [hvals hrel]] fdi.
  rewrite get_map_prog_name.
  move: hvals hrel => /= <- hrel.
  case: get_fundef => [fd | //] [= hcomp].
  exists fd => // hsem.
  split; first by apply (ec_while_sem_pre hrel).
  subst fdi fsi => si hinit.
  exists si => //.
  exists eq, eq.
  split => //.
  2: { move=> fr1 fr2 ->. by apply ec_while_sem_post. }
  rewrite /=; move: (create_env _ _) => env.
  clear -Pc Pi Pi_r.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)).
  { done. }
  { move=> ? c <-. by apply wequiv_nil. }
  { move=> i c Hi Hc ?? /= <-.
    rewrite -cat1s. eapply wequiv_cat. by apply Hi. by apply Hc.
  }
  { move=> x tg ty e ii ? i <-. by apply wequiv_assgn_eq. }
  { move=> xs t o als es ii ? i <-. by apply wequiv_opn_eq. }
  { move=> xs o es ii ? i <-. apply wequiv_syscall_eq => //. by move=>??->. }
  { move=> a ii ? i <-. by apply wequiv_assert_eq. }
  { move=> e c1 c2 Hc1 Hc2 ii ? i <-. apply wequiv_if_eq => //.
    case. by apply Hc1. by apply Hc2.
  }
  { move=> v dir lo hi c Hc ii ? i <-. eapply wequiv_for_eq => //.
    by apply Hc.
  }
  { move=> a cdo e info cwh Hcdo Hcwh ii env0 cf <-.
    rewrite /wequiv_rec /wequiv /wkequiv /wkequiv_io.
    setoid_rewrite isem_cmd_while_rotate.
    change (wequiv_rec (env1:=env0) (env2:=env0) p' p ev ev eq_spec eq
              (toec_while_i (MkI ii (Cwhile a cdo e info cwh)))
              (cdo ++ [:: MkI ii (Cwhile a [::] e info (cwh ++ cdo))])
              eq).
    apply (wequiv_cat (Hcdo _ _ erefl)).
    apply wequiv_while => //.
    + by apply wequiv_nil.
    + exact (wequiv_cat (Hcwh _ _ erefl) (Hcdo _ _ erefl)).
  }
  { move=> xs f als es ii env0 i <- /=.
    apply wequiv_call_wa with
      (Pf:=rpreF (eS:=eq_spec)) (Qf:= rpostF (eS:=eq_spec)) (Rvals := eq) (Rv := eq) => //.
    - move=> vals1 vals2 s1 s2 vs1 vs2 <- <- <-. by apply ec_while_sem_pre.
    - by intros; subst.
    - move=> vals1 vals2 fs1 fs2 fr1 fr2  [_ [/= <- ->]] ->.
      exact (ec_while_sem_post erefl erefl).
    - move=>???. by apply wequiv_fun_rec.
    - by move=> vals1 vals2 fs1 fs2 fr1 fr2 _ ->.
  }
  done.
Qed.

End PROOF.

