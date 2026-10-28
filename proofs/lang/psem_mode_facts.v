(* * From the partial mode to the total mode.

   In the partial mode an access that is out of bounds, not aligned or not
   initialised fails, and so does an operation whose safety condition does not
   hold; in the total mode they succeed. Where the partial mode succeeds, the
   total mode computes the same value: the reads, the operators, the
   instructions, the writes and the results of a function. Both modes leave
   undefined the outputs of an instruction whose initialisation condition does
   not hold, so the two runs go through the same states. The assertions and
   the contracts are evaluated in a way that does not depend on the mode.

   In the [total_init] mode, an output that the other modes leave undefined
   holds the default value of its type, the value a total read of an
   undefined variable gives. The states of a partial run and of a
   [total_init] run then agree on the total read of every variable, which is
   all that the expressions observe, but not on whether a variable is
   initialised: the relation holds for the programs whose assertions do not
   test it ([no_var_init_prog]). *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem psem_facts sopn_semi_facts sopn_facts.

(* ------------------------------------------------------------------------- *)
(* A success of the partial mode is a success of the total mode               *)

Lemma mk_semi_partialE tin tout safe err init (f : sem_prod tin (sem_tuple_t tout)) vs t :
  app_sopn tin (mk_semi (sm := partial) safe err init f) vs = ok t ->
  app_sopn tin (mk_semi (sm := total) safe err init f) vs = ok t.
Proof.
  rewrite /mk_semi !mk_semi_aux_app_sopnE.
  case: mapM2 => //= vs'; case: app_sopn => //= t'.
  by rewrite /check_safe /=; case: all.
Qed.

Section EXEC_SOPN.

Context {asm_op syscall_state : Type} {ep : EstateParams syscall_state} {asmop : asmOp asm_op}.

Lemma exec_sopn_partialE o vs vs' :
  exec_sopn (sm := partial) o vs = ok vs' -> exec_sopn (sm := total) o vs = ok vs'.
Proof.
  rewrite /exec_sopn /sopn_sem; case: assert => //= _.
  by rewrite /sopn_sem_ /semi; t_xrbindP => t /mk_semi_partialE -> <-.
Qed.

End EXEC_SOPN.

Section WRITES.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  (gd : glob_decls).

Lemma get_var_partialE vm x v :
  get_var (sm := partial) true vm x = ok v ->
  get_var (sm := total) true vm x = ok v.
Proof.
  rewrite /get_var /=.
  by case heq: is_defined => //= -[<-]; rewrite (Vm.get_totalE heq) heq.
Qed.

Lemma get_var_is_partialE vm xs vs :
  get_var_is (sm := partial) true vm xs = ok vs ->
  get_var_is (sm := total) true vm xs = ok vs.
Proof.
  elim: xs vs => [ | x xs ih] vs //=.
  by t_xrbindP => v /get_var_partialE -> vs' /ih -> <-.
Qed.

Lemma write_lval_partialE x v s s' :
  write_lval (sm := partial) true gd x v s = ok s' ->
  write_lval (sm := total) true gd x v s = ok s'.
Proof.
  case: x => //=.
  + move=> al ws _ e; t_xrbindP => p vp /sem_pexpr_partialE -> /= -> w -> m hw <-.
    by rewrite /= (write_totalE hw).
  + move=> al aa ws x e; apply on_arr_varP => n t htx /get_var_partialE hget.
    rewrite /on_arr_var hget /=; t_xrbindP => i vi /sem_pexpr_partialE -> /= -> w -> t' ht' hw.
    move: ht'; rewrite /WArray.set /= => ht'.
    by rewrite (write_totalE ht').
  move=> aa ws len x e; apply on_arr_varP => n t htx /get_var_partialE hget.
  rewrite /on_arr_var hget /=; t_xrbindP => i vi /sem_pexpr_partialE -> /= -> t1 -> t' ht' hw.
  by move: ht' hw; rewrite /WArray.set_sub /=; case: ifP => // _ [<-].
Qed.

Lemma write_lvals_partialE s xs vs s' :
  write_lvals (sm := partial) true gd s xs vs = ok s' ->
  write_lvals (sm := total) true gd s xs vs = ok s'.
Proof.
  elim: xs vs s => [ | x xs ih] [ | v vs] s //=.
  by t_xrbindP => s1 /write_lval_partialE -> /ih.
Qed.

End WRITES.

(* ------------------------------------------------------------------------- *)
(* The runs of the partial mode are runs of the [total_init] mode             *)

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

(* The assertions that do not test whether a variable is initialised. *)
Fixpoint no_var_init_eassert (a : eassert) : bool :=
  match a with
  | Pis_var_init _ => false
  | Pand a1 a2 => no_var_init_eassert a1 && no_var_init_eassert a2
  | Pexpr _ | PappN_safety _ _ | Pis_mem_init _ _ => true
  end.

Fixpoint no_var_init_i {asm_op : Type} {asmop : asmOp asm_op} (i : instr) : bool :=
  let: MkI _ ir := i in
  match ir with
  | Cassert a => no_var_init_eassert a.2
  | Cif _ c1 c2 => all no_var_init_i c1 && all no_var_init_i c2
  | Cfor _ _ c => all no_var_init_i c
  | Cwhile _ c1 _ _ c2 => all no_var_init_i c1 && all no_var_init_i c2
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Ccall _ _ _ => true
  end.

Definition no_var_init_prog {asm_op : Type} {asmop : asmOp asm_op} {pT : progT} (p : prog) :=
  all (fun f => all no_var_init_i (f_body f.2)) (p_funcs p).

Section ST_TOTAL.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  (gd : glob_decls).

(* Two states that agree on everything a total read observes. *)
Definition st_total (s1 s2 : estate) :=
  [/\ escs s1 = escs s2, emem s1 = emem s2
    & forall x, Vm.get (sm := total) (evm s1) x = Vm.get (sm := total) (evm s2) x].

Lemma st_total_refl s : st_total s s.
Proof. by split. Qed.

Lemma st_total_trans s1 s2 s3 : st_total s1 s2 -> st_total s2 s3 -> st_total s1 s3.
Proof. by move=> [h1 h2 h3] [h1' h2' h3']; split => [ | | x]; rewrite ?h1 ?h2 ?h3. Qed.

Lemma st_total_eq_on s1 s2 X : st_total s1 s2 -> eq_on (sm := total) X (evm s1) (evm s2).
Proof. by move=> [_ _ h] x _; apply h. Qed.

Lemma st_total_sem_pexpr wdb s1 s2 e :
  st_total s1 s2 ->
  sem_pexpr (sm := total) wdb gd s1 e = sem_pexpr (sm := total) wdb gd s2 e.
Proof. by move=> h; apply: eq_on_sem_pexpr; [case: h | apply: st_total_eq_on h]. Qed.

Lemma st_total_sem_pexprs wdb s1 s2 es :
  st_total s1 s2 ->
  sem_pexprs (sm := total) wdb gd s1 es = sem_pexprs (sm := total) wdb gd s2 es.
Proof. by move=> h; apply: eq_on_sem_pexprs; [case: h | apply: st_total_eq_on h]. Qed.

Lemma st_total_get_var_is wdb s1 s2 xs :
  st_total s1 s2 ->
  get_var_is (sm := total) wdb (evm s1) xs = get_var_is (sm := total) wdb (evm s2) xs.
Proof. by case=> _ _ h; elim: xs => //= x xs ->; rewrite /get_var h. Qed.

Lemma st_total_sem_eassert s1 s2 a :
  st_total s1 s2 -> no_var_init_eassert a -> sem_eassert gd s1 a = sem_eassert gd s2 a.
Proof.
  move=> h; have hm : emem s1 = emem s2 by case: h.
  elim: a => //=.
  + by move=> e _; rewrite (st_total_sem_pexpr _ _ h).
  + by move=> o es _; have := st_total_sem_pexprs true es h; rewrite /sem_pexprs => ->.
  + by move=> e1 e2 _; rewrite !(st_total_sem_pexpr _ _ h) hm.
  by move=> e1 he1 e2 he2 /andP [/he1 -> /he2 ->].
Qed.

Lemma st_total_write_lval wdb x v s1 s2 s1' :
  st_total s1 s2 ->
  write_lval (sm := total) wdb gd x v s1 = ok s1' ->
  exists2 s2', write_lval (sm := total) wdb gd x v s2 = ok s2' & st_total s1' s2'.
Proof.
  move=> hst hw.
  have [vm2 hw2 heq] :=
    write_lval_eq_on1 (vm1 := evm s2) (st_total_eq_on (X := read_rv x) hst) hw.
  have hs2 : with_vm s1 (evm s2) = s2 by case: hst => ?? _; apply: with_vm_evm.
  rewrite hs2 in hw2; exists (with_vm s1' vm2) => //; split => //= z.
  case: (Sv_memP z (vrv x)) => hz.
  + by apply: Vm.get_eq_mode => //; apply: heq.
  rewrite -(get_total_eq_ex (vrvP hw) hz).
  case: hst => _ _ ->.
  by apply: (get_total_eq_ex (vrvP hw2) hz).
Qed.

(* Writing the default value of an undefined boolean instead of the undefined
   value gives the same total reads. *)
Lemma st_total_write_lval_dflt x v s s' :
  write_lval (sm := total) true gd x v s = ok s' ->
  exists2 s'', write_lval (sm := total) true gd x (value_dflt v) s = ok s'' & st_total s' s''.
Proof.
  rewrite /value_dflt; case: ifP => hdef; first by move=> ->; exists s' => //; apply: st_total_refl.
  case: v hdef => // t h _.
  case: x => /=.
  + move=> _ ty /write_noneP [-> htr].
    rewrite /DB /= => /eqP ?; subst t; move: htr; rewrite /write_none /=.
    by move=> /eqP <- /=; exists s => //; apply: st_total_refl.
  + move=> x; rewrite /write_var; t_xrbindP => vm /set_varP [hdb htr ->] <-.
    move: hdb htr; rewrite /DB /= => /eqP ?; subst t => /eqP htx.
    rewrite /= set_var_truncate //=; last by rewrite -htx.
    eexists; first reflexivity; split => //= z.
    by rewrite !(Vm.get_modeE (sm := total)) !Vm.setP; case: eqP => // <-; rewrite -htx /=.
  + by move=> al ws _ e; t_xrbindP => p vp hvp hp w hw; case: t h hw.
  + move=> al aa ws x e; apply on_arr_varP => n t0 _ _.
    by t_xrbindP => i vi hvi hi w hw; case: t h hw.
  move=> aa ws len x e; apply on_arr_varP => n t0 _ _.
  by t_xrbindP => i vi hvi hi a ha; case: t h ha.
Qed.

Lemma st_total_write_lvals s1 s2 xs vs s1' :
  st_total s1 s2 ->
  write_lvals (sm := total) true gd s1 xs vs = ok s1' ->
  exists2 s2', write_lvals (sm := total) true gd s2 xs vs = ok s2' & st_total s1' s2'.
Proof.
  elim: xs vs s1 s2 => [ | x xs ih] [ | v vs] s1 s2 //=; first by move=> h [<-]; exists s2.
  by move=> h; t_xrbindP => s1a /(st_total_write_lval h) [s2a -> ha] /(ih _ _ _ ha).
Qed.

Lemma st_total_write_lvals_dflt s1 s2 xs vs s1' :
  st_total s1 s2 ->
  write_lvals (sm := total) true gd s1 xs vs = ok s1' ->
  exists2 s2', write_lvals (sm := total) true gd s2 xs (map value_dflt vs) = ok s2'
             & st_total s1' s2'.
Proof.
  elim: xs vs s1 s2 => [ | x xs ih] [ | v vs] s1 s2 //=; first by move=> h [<-]; exists s2.
  move=> h; t_xrbindP => s1a /st_total_write_lval_dflt [s1b /(st_total_write_lval h) [s2b -> hb] hab].
  by move=> /(ih _ _ _ (st_total_trans hab hb)).
Qed.

(* From a partial run to a [total_init] run. *)

Lemma st_total_sem_pexpr_partial e :
  wrequiv st_total (fun s => sem_pexpr (sm := partial) true gd s e)
                   (fun s => sem_pexpr (sm := total_init) true gd s e) eq.
Proof.
  move=> s1 s2 v h /sem_pexpr_partialE; rewrite (st_total_sem_pexpr _ _ h).
  by rewrite (sem_pexpr_is_totalE gd (sm2 := total_init)) // => ->; exists v.
Qed.

Lemma st_total_sem_pexprs_partial es :
  wrequiv st_total (fun s => sem_pexprs (sm := partial) true gd s es)
                   (fun s => sem_pexprs (sm := total_init) true gd s es) eq.
Proof.
  move=> s1 s2 v h /sem_pexprs_partialE; rewrite (st_total_sem_pexprs _ _ h).
  by rewrite (sem_pexprs_is_totalE gd (sm2 := total_init)) // => ->; exists v.
Qed.

Lemma st_total_write_lval_partial x v :
  wrequiv st_total (write_lval (sm := partial) true gd x v)
                   (write_lval (sm := total_init) true gd x v) st_total.
Proof.
  move=> s1 s2 s1' h /write_lval_partialE hw.
  by rewrite -(write_lval_is_totalE gd (sm1 := total)) //; apply: st_total_write_lval h hw.
Qed.

Lemma st_total_write_lvals_partial xs vs1 vs2 :
  vs2 = vs1 \/ vs2 = map value_dflt vs1 ->
  wrequiv st_total (fun s => write_lvals (sm := partial) true gd s xs vs1)
                   (fun s => write_lvals (sm := total_init) true gd s xs vs2) st_total.
Proof.
  move=> hvs s1 s2 s1' h /write_lvals_partialE hw.
  rewrite -(write_lvals_is_totalE gd (sm1 := total)) //.
  by case: hvs => ->; [exact: st_total_write_lvals h hw | exact: st_total_write_lvals_dflt h hw].
Qed.

End ST_TOTAL.

Section PROOF_INIT.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {wa : WithAssert}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : uprog) (ev : extra_val_t).

Notation wequiv_c :=
  (wequiv_rec (wa1 := wa) (wa2 := wa) (sm1 := partial) (sm2 := total_init) p p ev ev eq_spec).

Let Pi (i : instr) := no_var_init_i i -> wequiv_c st_total [:: i] [:: i] st_total.

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) := all no_var_init_i c -> wequiv_c st_total c c st_total.

Lemma partial_total_init_aux :
  no_var_init_prog p ->
  forall fn,
  wiequiv_f (wa1 := wa) (wa2 := wa) (sm1 := partial) (sm2 := total_init)
    p p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
  move=> hp fn; apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd hfd.
  exists fd => //; move=> hpre; split => // s hinit; exists s => //.
  exists st_total, st_total; split.
  + exact: st_total_refl.
  3: by move=> ?? ->.
  2: { move=> s1 s2 fr h; rewrite /finalize_funcall; t_xrbindP => vs /get_var_is_partialE.
       rewrite (st_total_get_var_is _ _ h) => hvs.
       have -> : get_var_is (sm := total_init) true (evm s2) (f_res fd) = ok vs.
       + by rewrite -hvs /get_var_is; apply: mapM_ext => x _; apply: get_var_is_totalE.
       by case: h => <- <- _ vs' /= -> <-; eexists; first reflexivity. }
  have : all no_var_init_i (f_body fd).
  + move: hp (get_fundef_in' hfd); rewrite /no_var_init_prog.
    by elim: (p_funcs p) => //= -[fn' fd'] fds ih /andP [h1 h2] [[_ <-] // | /(ih h2)].
  change (Pc (f_body fd)); apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
  + by move=> _; apply wequiv_nil.
  + move=> i c hi hc /= /andP [/hi {}hi /hc {}hc]; rewrite -cat1s.
    by apply wequiv_cat with st_total.
  + move=> x tg ty e ii _; apply wequiv_assgn_eq; first exact: st_total_sem_pexpr_partial.
    by move=> v; apply st_total_write_lval_partial.
  + move=> xs t o es ii _; apply wequiv_opn with eq (fun vs1 vs2 => vs2 = map value_dflt vs1).
    + exact: st_total_sem_pexprs_partial.
    + move=> _ _ _ vs _ vs' <- /exec_sopn_partialE h.
      by rewrite exec_sopn_total_initE h /=; eexists.
    by move=> vs1 vs2 ->; apply st_total_write_lvals_partial; right.
  + move=> xs o es ii _; apply wequiv_syscall_eq.
    + by move=> ?? [].
    + exact: st_total_sem_pexprs_partial.
    + by move=> fs1 fs2 fs1' <- h; exists fs1'.
    move=> fs'; rewrite /upd_estate => s1 s2 s1' h.
    apply: (st_total_write_lvals_partial (or_introl erefl)).
    by case: h.
  + move=> a ii /= ha; apply wequiv_assert_eq => // ha1; split => //.
    by move=> s1 s2 b h; rewrite (st_total_sem_eassert _ h ha) => ->; exists b.
  + move=> e c1 c2 hc1 hc2 ii /= /andP [/hc1 {}hc1 /hc2 {}hc2]; apply wequiv_if_eq.
    + exact: st_total_sem_pexpr_partial.
    by case.
  + move=> v dir lo hi c hc ii /= /hc {}hc; apply wequiv_for_eq with st_total => //.
    + exact: st_total_sem_pexprs_partial.
    move=> i s1 s2 s1' h hw.
    exact: (st_total_write_lval_partial (gd := p_globs p) (x := Lvar v) h hw).
  + move=> a c e info c' hc hc' ii /= /andP [/hc {}hc /hc' {}hc'].
    apply wequiv_while_eq => //.
    exact: st_total_sem_pexpr_partial.
  move=> xs f es ii _; apply wequiv_call_eq_wa.
  + exact: st_total_sem_pexprs_partial.
  + by move=> s1 s2 vs [h1 h2 _]; rewrite /mk_fstate h1 h2.
  + by move=> s1 s2 vs [h1 h2 _]; rewrite /mk_fstate h1 h2.
  + exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p p ev ev eq_spec ii ii f f).
  + by [].
  move=> fs'; rewrite /upd_estate => s1 s2 s1' h.
  apply: (st_total_write_lvals_partial (or_introl erefl)).
  by case: h.
Qed.

End PROOF_INIT.

Lemma partial_total_init :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {wa : WithAssert}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : uprog) (ev : extra_val_t),
  no_var_init_prog p ->
  forall fn,
  wiequiv_f (wa1 := wa) (wa2 := wa) (sm1 := partial) (sm2 := total_init)
    p p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof. exact: @partial_total_init_aux. Qed.
