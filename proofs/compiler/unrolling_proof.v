(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ZArith.
Require Import psem compiler_util.
Require Export unrolling.

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

  Section SEM.

  Let Pi_r s (i:instr_r) s' :=
    forall ii, sem p' ev s (unroll_i (MkI ii i)).1 s'.

  Let Pi s (i:instr) s' :=
    sem p' ev s (unroll_i i).1 s'.

  Let Pc s (c:cmd) s':=
    sem p' ev s (unroll_cmd unroll_i c).1 s'.

  Let Pfor (i:var_i) vs s c s' :=
    sem_for p' ev i vs s (unroll_cmd unroll_i c).1 s'
    /\ forall ii, sem p' ev s
      (flatten (map (fun n => assgn ii i (Pconst n) :: (unroll_cmd unroll_i c).1) vs)) s'.

  Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
    sem_call p' ev scs1 m1 fn vargs scs2 m2 vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. exact: Eskip. Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move => s1 s2 s3 i c _.
    rewrite /Pi /Pc /=.
    case: unroll_i => i' b Hi _.
    case: unroll_cmd => c' a Hc.
    exact: sem_app Hi Hc.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. move=> ii i s1 s2 _ Hi; exact: Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hv hv' hw ii.
    by apply: sem_seq1; apply: EmkI; apply: Eassgn; rewrite ?p'_globs; eassumption.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es Hw ii.
    by apply: sem_seq1; apply: EmkI; apply: Eopn; rewrite ?p'_globs; eassumption.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 xs o es ves vs hes ho hw ii /=.
    apply: sem_seq1; apply: EmkI; apply: Esyscall; rewrite ?p'_globs; eassumption.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 Hb _.
    rewrite /Pc /Pi_r /=.
    case: unroll_cmd => c1' b1 /= Hc ii.
    case: unroll_cmd => c2' b2 /=.
    by apply: sem_seq1; apply: EmkI; apply: Eif_true; rewrite ?p'_globs.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 Hb _.
    rewrite /Pc /Pi_r /=.
    case: unroll_cmd => c2' b2 /= Hc ii.
    case: unroll_cmd => c1' b1 => /=.
    by apply: sem_seq1; apply: EmkI; apply: Eif_false; rewrite ?p'_globs.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c1 e ei c2 _.
    rewrite /Pc /Pi_r /=.
    case: (unroll_cmd _ c1) => c1' b1 /= Hc1 Hb _.
    case: (unroll_cmd _ c2) => c2' b2 /= Hc2 _ Hi ii.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_true; rewrite ?p'_globs; eauto.
    by move: Hi=> /(_ ii) /semE [?] [/sem_IE Hi /semE ->].
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move => s1 s2 a c1 e ei c2 _.
    rewrite /Pc /Pi_r /=.
    case: (unroll_cmd _ c1) => c1' b1 /= Hc1 Hb ii.
    case: (unroll_cmd _ c2) => c2' b2 /=.
   by apply: sem_seq1; apply: EmkI; apply: Ewhile_false; rewrite ?p'_globs.
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi Hlo Hhi _ [].
    rewrite /Pi_r /=.
    case: unroll_cmd => c' b /= Hfor Hfor' ii.
    case Hlo': (is_const lo)=> [nlo|].
    + case Hhi': (is_const hi)=> [nhi|].
      + have ->: nlo = vlo.
          rewrite /is_const /= in Hlo'.
          by case: lo Hlo Hlo'=> //= z [] -> [] ->.
        have ->: nhi = vhi.
          rewrite /is_const /= in Hhi'.
          by case: hi Hhi Hhi'=> //= z [] -> [] ->.
        exact: Hfor'.
    all: apply: sem_seq1; apply: EmkI; apply: Efor; rewrite ?p'_globs; eassumption.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move => s i c; split => /=; first by exact: EForDone.
    move=> ii; apply: Eskip.
  Qed.

  Lemma write_var_Z i (z: Z) s s' :
    write_var true i z s = ok s' ->
    eval_atype (vtype i) = cint.
  Proof. by case: i => - [[] x]. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hw Hsc Hc Hsfor [Hfor Hfor']; split=> [|ii].
    apply: EForOne; [exact: Hw|exact: Hc|exact: Hfor].
    move: Hfor'=> /(_ ii) Hfor'.
    apply: Eseq.
    + apply: EmkI; apply: Eassgn;[ reflexivity | by rewrite (write_var_Z Hw) | exact Hw].
    apply: sem_app; [ exact: Hc | exact: Hfor'].
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs Hexpr _ Hfun Hw ii' /=.
    by apply: sem_seq1; apply: EmkI; apply: Ecall; rewrite ?p'_globs; eassumption.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move => scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres'.
    case: f=> fi ftyi fparams fc ftyo fres fe /= Hget Htyi Hi Hw _ Hc Hres Htyo Hsys Hfi.
    move/p'_get_fundef: Hget Hc.
    rewrite /Pc /=.
    case: unroll_cmd => c _ /= Hget Hc.
    apply: EcallRun; first exact: Hget.
    all: rewrite /= ?p'_extra; eassumption.
  Qed.

  Lemma unroll_callP f scs mem scs' mem' va vr:
    sem_call p  ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
    exact:
      (sem_call_Ind
         Hskip
         Hcons
         HmkI
         Hassgn
         Hopn
         Hsyscall
         Hif_true
         Hif_false
         Hwhile_true
         Hwhile_false
         Hfor
         Hfor_nil
         Hfor_cons
         Hcall
         Hproc).
  Qed.

  End SEM.

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
    move=> s {hfd}.
    case: fd => /= finfo ftyin fparams fbody ftyout fres fextra.
    case heq: unroll_cmd => [c' b] /= hinit.
    exists s.
    + by move: hinit; rewrite /initialize_funcall /= p'_extra.
    exists (st_eq tt), (st_eq tt); split => //.
    2: by apply st_eq_finalize.
    have -> : c' = (unroll_cmd unroll_i fbody).1 by rewrite heq.
    clear heq hinit c' b fn fs s finfo ftyin fparams ftyout fres fextra.
    apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => // {fbody}; rewrite /Pi_r /Pi /Pc.
    + by apply wequiv_nil.
    + by move=> > hi hc /=; surjpairing; rewrite /= -cat1s; apply wequiv_cat with (st_eq tt).
    + by move=> ????? /=; apply wequiv_assgn_rel_eq with checker_st_eq tt.
    + by move=> ????? /=; apply wequiv_opn_rel_eq with checker_st_eq tt.
    + by move=> ???? /=; apply wequiv_syscall_rel_eq with checker_st_eq tt.
    + by move=> ?? /=; apply wequiv_assert_rel_eq with checker_st_eq.
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
