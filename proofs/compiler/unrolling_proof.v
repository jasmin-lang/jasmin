(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ZArith.
Require Import psem compiler_util.
Require Export unrolling.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Local Open Scope seq_scope.

Section PROOF.

  Context
    {wsw : WithSubWord}
    {dc:DirectCall}
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    {pT : progT}
    {sCP : semCallParams}.

  Variable (p : prog) (ev:extra_val_t).
  Notation gd := (p_globs p).

  Let p' := (unroll_prog p).1.

  Lemma p'_globs : p_globs p' = p_globs p.
  Proof. by rewrite /p' /unroll_prog; case: map_repeat. Qed.

  Lemma p'_extra : p_extra p' = p_extra p.
  Proof. by rewrite /p' /unroll_prog; case: map_repeat. Qed.

  Lemma p'_get_fundef fn fd :
    get_fundef (p_funcs p) fn = Some fd ->
    get_fundef (p_funcs p') fn = Some (unroll_fun (fn, fd)).1.2.
  Proof.
    rewrite /p' /unroll_prog.
    have := map_repeat_1 unroll_fun (p_funcs p).
    case: map_repeat => _ b /= ->.
    rewrite /get_fundef assoc_mapE; last first.
    - by move => ? [] > /=; case unroll_cmd.
    by move => ->.
  Qed.

  Lemma write_var_Z i (z: Z) s s' :
    write_var true i z s = ok s' ->
    eval_atype (vtype i) = cint.
  Proof. by case: i => - [[] x]. Qed.

  Section IT.

  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  Let Pi (i:instr) :=
    wequiv_rec p p' ev ev eq_spec (st_eq tt) [::i] (unroll_i i).1 (st_eq tt).

  Let Pi_r i := forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) := wequiv_rec p p' ev ev eq_spec (st_eq tt) c (unroll_cmd unroll_i c).1 (st_eq tt).

  #[local] Lemma _checker_st_eqP : Checker_eq p p' checker_st_eq.
  Proof. by apply checker_st_eqP; rewrite p'_globs. Qed.
  #[local] Hint Resolve _checker_st_eqP : core.

  Ltac surjpair1 :=
    match goal with
    |- context [let '(_,_) := ?x in _] => rewrite (surjective_pairing x)
    end.
  Ltac surjpairing := repeat surjpair1.

  Lemma it_unroll_callP fn :
    wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
  Proof.
    apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hfd.
    exists (unroll_fun (fn, fd)).1.2.
    + by apply: p'_get_fundef hfd.
    move=> s {hfd} hinit.
    exists s.
    + by move: hinit; rewrite /initialize_funcall /= p'_extra.
    exists (st_eq tt), (st_eq tt); split => //.
    2: by apply st_eq_finalize.
    move=> {s hinit}.
    apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => //; rewrite /Pi_r /Pi /Pc.
    + by apply wequiv_nil.
    + by move=> > hi hc /=; surjpairing; rewrite /= -cat1s; apply wequiv_cat with (st_eq tt).
    + by move=> ????? /=; apply wequiv_assgn_rel_eq with checker_st_eq tt.
    + by move=> ????? /=; apply wequiv_opn_rel_eq with checker_st_eq tt.
    + by move=> ???? /=; apply wequiv_syscall_rel_eq with checker_st_eq tt.
    + by move=> ?? /=; apply wequiv_noassert.
    + by move=> > ??? /=; surjpairing; apply wequiv_if_rel_eq with checker_st_eq tt tt tt.
    + move=> i d lo hi c hc ii /=; surjpairing.
      case: is_constP => [{}lo | {}lo]; last by apply wequiv_for_rel_eq with checker_st_eq tt tt.
      case: is_constP => [{}hi | {}hi]; last by apply wequiv_for_rel_eq with checker_st_eq tt tt.
      rewrite /wequiv_rec /wequiv.
      apply (wkequiv_eutt_l (F1 := fun s => isem_for_loop isem_i_body p ev i c (wrange d lo hi) s)).
      + move=> s1 _ _ /=; rewrite /isem_bound /sem_bound /=.
        rewrite ITree.Eq.Eqit.bind_ret_l ITree.Eq.Eqit.bind_ret_r; reflexivity.
      elim: wrange => [ | j js hjs] /=.
      + by apply wkequiv_ret.
      rewrite /isem_for_round.
      set c' := (unroll_cmd _ _).1.
      apply wkequiv_bind with (st_eq tt).
      + apply wkequiv_iresult.
        move=> s t s' /st_relP [-> /= heq] hw.
        rewrite /sem_assgn /= (write_var_Z hw) /=.
        have [vm2 /= ??] := [elaborate write_lvar_ext_eq (gd := [::]) (x:= Lvar i) heq hw].
        by exists (with_vm s' vm2).
      apply (wkequiv_eutt_r
              (F2 := fun s => Monad.bind (isem_cmd_ p' ev c' s)
                      [eta isem_cmd_ p' ev (flatten [seq assgn ii i (Pconst n) :: c' | n <- js])])).
      + move=> _ s2 _; rewrite isem_cmd_cat; reflexivity.
      by apply wkequiv_bind with (st_eq tt).
    + by move=> > hc hc' ii /=; surjpairing; apply wequiv_while_rel_eq with checker_st_eq tt.
    move=> ???? /=; surjpairing; apply wequiv_call_rel_eq with checker_st_eq tt => //.
    by move=> ???; apply: wequiv_fun_rec.
  Qed.

  End IT.

End PROOF.
