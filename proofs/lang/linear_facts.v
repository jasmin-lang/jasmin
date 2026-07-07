From Coq Require Import Relations Lia Utf8.

From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Require Import
  while
  fexpr_facts
  label
  linear
  linear_sem
  one_varmap
  psem
  psem_facts
  sem_one_varmap
  hoare_logic
.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Notation nify := (addnE, rwR2 (@leP), rwR2 (@andP), rwR1 (@negP)).

Ltac simpl_size :=
  do ?(rewrite !(size_cat, size_rcons) /=);
  rewrite /= ?nify.

Section WITH_PARAMS.

#[local] Existing Instance withsubword.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
.

Lemma setpc_id ls :
  setpc ls (lpc ls) = ls.
Proof. by case: ls. Qed.

Lemma setpc_lset_estate ls pc scs m vm :
  lset_estate (setpc ls pc) scs m vm
  = setpc (lset_estate ls scs m vm) pc.
Proof. done. Qed.

Lemma lnext_pc_setpc ls n :
  lnext_pc (setpc ls n) = setpc ls n.+1.
Proof. done. Qed.

Lemma setcpc_setpc ls fn n n' :
  setcpc (setpc ls n') fn n = setcpc ls fn n.
Proof. done. Qed.

Lemma lfn_lset_estate ls scs m vm :
  lfn (lset_estate ls scs m vm) = lfn ls.
Proof. done. Qed.


Lemma label_in_lcmd_cat lc1 lc2 :
  label_in_lcmd (lc1 ++ lc2) = label_in_lcmd lc1 ++ label_in_lcmd lc2.
Proof. by rewrite /label_in_lcmd pmap_cat. Qed.

Lemma find_labelE lbl c :
  find_label lbl c =
  if c is i :: c'
  then
    if is_label lbl i
    then ok O
    else Let r := find_label lbl c' in ok r.+1
  else type_error.
Proof.
  case: c => // i c; rewrite /find_label /=.
  case: (is_label lbl i) => //.
  rewrite ltnS.
  by case: ifP.
Qed.

Lemma find_label_cat_hd lbl c1 c2:
  ~~ has (is_label lbl) c1 ->
  find_label lbl (c1 ++ c2)
  = Let pc := find_label lbl c2 in ok (size c1 + pc).
Proof.
  rewrite /find_label find_cat size_cat => /negbTE ->.
  by rewrite ltn_add2l;case:ifP.
Qed.

Definition is_linear_of (lp : lprog) (fn : funname) (lc : lcmd) : Prop :=
  exists2 fd,
    get_fundef (lp_funcs lp) fn = Some fd
    & lfd_body fd = lc.

Lemma label_in_lfundef p fn body (lbl: label) :
  lbl \in label_in_lcmd body ->
  is_linear_of p fn body ->
  (fn, lbl) \in label_in_lprog p.
Proof.
  move=> hin [fd ok_fd ?]; subst body.
  apply/flattenP => /=.
  exists [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd) ];
    last by apply/map_f: hin.
  apply/in_map.
  by exists (fn, fd); first exact: get_fundef_in'.
Qed.

Lemma find_instrE lp ls body :
  is_linear_of lp (lfn ls) body ->
  find_instr lp ls = oseq.onth body (lpc ls).
Proof. by rewrite /find_instr => - [] fd /= -> ->. Qed.

Lemma find_instr_skip' lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls n,
    lpc ls = size pre + n ->
    lfn ls = fn ->
    find_instr lp ls = oseq.onth pos n.
Proof.
  move=> h ls n hpc hfn.
  rewrite -hfn in h.
  rewrite (find_instrE h) !oseq.onth_nth map_cat nth_cat size_map.
  by rewrite hpc lt_nm_n sub_nmn.
Qed.

Lemma find_instr_skip lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls n,
    lfn ls = fn ->
    find_instr lp (setpc ls (size pre + n)) = oseq.onth pos n.
Proof. by eauto using find_instr_skip'. Qed.

Lemma find_instr_skip0 lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls,
    lpc ls = size pre ->
    lfn ls = fn ->
    find_instr lp ls = oseq.onth pos 0.
Proof. rewrite -(addn0 (size pre)). by eauto using find_instr_skip'. Qed.

Lemma eval_jumpE lp fn body :
  is_linear_of lp fn body ->
  forall lbl s,
    eval_jump lp (fn, lbl) s
    = Let pc := find_label lbl body in ok (setcpc s fn pc.+1).
Proof. by case => ? /= -> ->. Qed.

Lemma eval_jumpP lp fn lfd lbl lbl' :
  get_fundef (lp_funcs lp) fn = Some lfd ->
  find_label lbl (lfd_body lfd) = ok lbl' ->
  eval_jump lp (fn, lbl) = fun ls => ok (setcpc ls fn lbl'.+1).
Proof. by rewrite /eval_jump => -> /= ->. Qed.

Section MEM_EQUIV.

Lemma eval_jump_mem_eq lp r s1 s2 :
  eval_jump lp r s1 = ok s2 ->
  lmem s1 = lmem s2.
Proof.
  case: r => fn lbl /=.
  case: get_fundef => [lfd|//] /=.
  by t_xrbindP=> _ _ <- /=.
Qed.

Lemma eval_instr_mem_equiv lp i s1 s2 :
  eval_instr lp i s1 = ok s2 ->
  mem_equiv (lmem s1) (lmem s2).
Proof.
Opaque eval_jump.
  rewrite /eval_instr.
  case: i => [ii []] /=.
  + t_xrbindP=> ???? _ ? _ ? hw <- /=.
    split.
    + exact: write_lexprs_stack_stable hw.
    exact: write_lexprs_validw hw.
    + t_xrbindP=> ?? _ [[??]?] /(exec_syscallSs (rscs := _)) heq1.
    t_xrbindP=> ? hw <- /=.
    apply (mem_equiv_trans heq1).
    split.
    + exact: write_lvals_stack_stable hw.
    exact: write_lvals_validw hw.
  + move=> [p|].
    + by t_xrbindP=> _ _ _ _ _ _ _ _ /eval_jump_mem_eq /= <-.
    t_xrbindP=> ??? _ _ _ _ _ w _ ? hw /eval_jump_mem_eq /= <-.
    split.
    + exact: Memory.write_mem_stable hw.
    by move=> ???; rewrite (write_validw_eq hw).
  + by t_xrbindP=> _ _ _ _ _ _ _ _ /eval_jump_mem_eq /= <-.
  + by move=> [<-] /=.
  + by move=> _ _ [<-] /=.
  + by move=> _ /eval_jump_mem_eq /= <-.
  + by t_xrbindP=> _ _ _ _ _ r _ /eval_jump_mem_eq <-.
  + by t_xrbindP=> _ _ _ _ _ _ <- /=.
  t_xrbindP=> ?? b ? _ _.
  case: b.
  + by move=> /eval_jump_mem_eq <-.
  by move=> [<-] /=.
Transparent eval_jump.
Qed.


Lemma lsem1_mem_equiv lp s1 s2 :
  step lp s1 = ok s2 ->
  mem_equiv (lmem s1) (lmem s2).
Proof.
  rewrite /step.
  case: find_instr => [i|//].
  exact: eval_instr_mem_equiv.
Qed.

Lemma lsem_n_0 lp cond s :
  lsem_n lp cond s s.
Proof. by exists 0. Qed.

Lemma lsem_n_eval_lin lp n i s2 s1 s3 c1 c2 fn :
  is_linear_of lp fn (c1 ++ c2) ->
  lfn s1 = fn ->
  lpc s1 = size c1 + n ->
  oseq.onth c2 n = Some i ->
  eval_instr lp i s1 = ok s2 ->
  lsem_n lp (endpc lp fn) s2 s3 ->
  lsem_n lp (endpc lp fn) s1 s3.
Proof.
  move=> hlin hfn hpc hi hev; apply lsem_n_endpc_step => //.
  by rewrite /step (find_instr_skip' hlin hpc) // hi.
Qed.

Lemma lsem_n_eval_lin1 lp n i s1 s2 c1 c2 fn :
  is_linear_of lp fn (c1 ++ c2) ->
  lfn s1 = fn ->
  lpc s1 = size c1 + n ->
  oseq.onth c2 n = Some i ->
  eval_instr lp i s1 = ok s2 ->
  lsem_n lp (endpc lp fn) s1 s2.
Proof.
  move=> hlin hfn hpc hi hev.
  apply: lsem_n_eval_lin hlin hfn hpc hi hev (lsem_n_0 lp (endpc lp fn) s2).
Qed.

Lemma lsem_n_step_end lp fn s2 s1 s3 :
  lsem_n lp (endpc lp fn) s1 s2 ->
  step lp s2 = ok s3 ->
  lsem_n lp (endpc lp fn) s1 s3.
Proof.
  move=> hsem hstep.
  apply: (lsem_n_trans hsem).
  apply (lsem_n_endpc_step hstep).
  apply lsem_n_0.
Qed.

Lemma endpc_untilpc lp fn fd :
  get_fundef (lp_funcs lp) fn = Some fd ->
  endpc lp fn =1 untilpc (fn, size (lfd_body fd)).
Proof.
  rewrite /endpc /untilpc => -> s0; case: eqP.
  + move=> -> /=; case: eqP.
    + by move=> ->; rewrite eqxx.
    by move=> h; symmetry; apply /eqP => /= -[] h1; apply h; rewrite h1.
  by move=> h; symmetry; apply /eqP => -[].
Qed.

Section ITREE.

Context {E E0: Type -> Type} {wE: with_Error E E0}.

Lemma ilsem_mem_equiv lp cond m :
  khoare (iE0 := trivial_invEvent E0) (iEr := invErrT)
    (fun s => mem_equiv m (lmem s))
    (ilsem lp cond)
    (fun s => mem_equiv m (lmem s)).
Proof.
  apply khoare_iter.
  rewrite /while_body => s hmem /=.
  case: ifP => _; last by apply core_logics.lutt_Ret.
  apply core_logics.lutt_bind with (fun s => mem_equiv m (lmem s)); last by move=> *; apply core_logics.lutt_Ret.
  rewrite /istep; case heq: step => [s' | e] /=.
  + apply core_logics.lutt_Ret.
    by apply: mem_equiv_trans (lsem1_mem_equiv heq).
  apply core_logics.lutt_Vis => //=.
  by rewrite /preInv /= /Subevent.subevent /= /CategoryOps.resum /= /fromErr mid12.
Qed.

End ITREE.

End MEM_EQUIV.

Lemma sem_fopns_args_cat s lc1 lc2 :
  sem_fopns_args s (lc1 ++ lc2) =
  Let s' := sem_fopns_args s lc1 in sem_fopns_args s' lc2.
Proof. apply foldM_cat. Qed.

Lemma sem_fopn_args_eval_instr ls s' lp a ii :
  sem_fopn_args a (to_estate ls) = ok s' ->
  let: ls' := lnext_pc (lset_estate' ls s') in
  eval_instr lp (li_of_fopn_args ii a) ls = ok ls'.
Proof.
  move: a => [[les op] res].
  rewrite /sem_fopn_args /eval_instr /= /to_estate /=.
  by t_xrbindP=> ? -> /= ? -> /= ->.
Qed.

Lemma lsem_body_weak lp (cond1 cond2:lstate -> bool) s1 s2 :
  (forall s, cond1 s -> cond2 s) ->
  lsem_body lp cond1 s1 = ok (inl s2) -> lsem_body lp cond2 s1 = ok (inl s2).
Proof. by rewrite /lsem_body => /(_ s1); case: cond1 => // ->. Qed.

Lemma lsem_n_weak lp (cond1 cond2:lstate -> bool) s1 s2 :
  (forall s, cond1 s -> cond2 s) ->
  lsem_n lp cond1 s1 s2 -> lsem_n lp cond2 s1 s2.
Proof.
  move=> hcond [n hsem]; exists n.
  elim: n s1 hsem => //= n ih s1.
  have /(_ lp s1) := lsem_body_weak hcond.
  by case: lsem_body => //= -[] // ? /(_ _ erefl) -> /= /ih.
Qed.

Definition pc_between fn pcs pce (s:lstate) :=
  if lfn s == fn then pcs <= lpc s < pce
  else false.

Lemma pc_between_weak fn pcs1 pce1 pcs2 pce2 s :
  pcs2 <= pcs1 -> pce1 <= pce2 ->
  pc_between fn pcs1 pce1 s -> pc_between fn pcs2 pce2 s.
Proof.
  rewrite /pc_between; case: ifP => // _ hs he /andP [] hle hlt.
  by rewrite (leq_trans hs hle) /= (leq_trans hlt he).
Qed.


(* ----------------------------------------------------------------------- *)
(* Some properties about the compilation scheme and mix_ilstep             *)

Context {E E0: Type -> Type} {wE: with_Error E E0}.
Context (lp : lprog).

Lemma mix_ilsteps_0 p1 cond ls : ~~cond ls -> mix_ilsteps p1 cond ls ≅ Ret ls.
Proof. by rewrite /mix_ilsteps while.unfold_while => /negbTE ->; reflexivity. Qed.

Definition pc_between_c fn (P l : lcmd) :=
  pc_between fn (size P) (size P + size l).

Lemma mix_ilsteps_split pcs' pce' pcs pce fn ls :
  pcs <= pcs' -> pce' <= pce ->
  mix_ilsteps lp (pc_between fn pcs pce) ls ≅
  ITree.bind (mix_ilsteps lp (pc_between fn pcs' pce') ls)
       (mix_ilsteps lp (pc_between fn pcs pce)).
Proof.
  move=> h1 h2; apply while.split_while_imp.
  rewrite /pc_between => i.
  case: ifP => // _ /andP [h1' h2'].
  by rewrite (leq_trans h1 h1') (leq_trans h2' h2).
Qed.

Lemma mix_ilsteps_split_c P' Q' P Q fn ls :
  size P <= size P' -> size P' + size Q' <= size P + size Q ->
  mix_ilsteps lp (pc_between_c fn P Q) ls ≅
  ITree.bind (mix_ilsteps lp (pc_between_c fn P' Q') ls)
       (mix_ilsteps lp (pc_between_c fn P Q)).
Proof. by move=> h1 h2; apply mix_ilsteps_split. Qed.

Lemma mix_ilsteps_b0 fn ls pcs pce :
  lfn ls = fn ->
  lpc ls = pce ->
  mix_ilsteps lp (pc_between fn pcs pce) ls ≅ Ret ls.
Proof.
  move=> hfn hpc; apply mix_ilsteps_0.
  rewrite /pc_between hfn hpc eqxx ?nify; lia.
Qed.

Definition is_Lcall i := if i is Lcall _ d then Some d.1 else None.

(* FIXME: move this *)
Lemma onth_nth_size {T: Type} (x0: T) s i :
  i < size s ->
  oseq.onth s i = Some (nth x0 s i).
Proof.
  elim: i s => [ | i ih] [ | x s] //=; apply ih.
Qed.

Notation Lilabel := (linear.Llabel InternalLabel).
Definition dummy_linstr := MkLI dummy_instr_info Lalign.

Lemma step_mix_ilsteps_eq_itree fn P Q pcs pce ls  :
  is_linear_of lp fn (P ++ Q) ->
  lfn ls = fn -> lpc ls = size P ->
  pcs <= size P < pce ->
  0 < size Q ->
  mix_ilsteps lp (pc_between fn pcs pce) ls ≅
  match eval_instr lp (nth dummy_linstr Q 0) ls with
  | Ok ls2 =>
    if is_Lcall (li_i (nth dummy_linstr Q 0)) is Some fn' then
       ITree.bind (trigger_inl1 (mix_to_small_steps.Call fn' ls2))
        (λ ls3, if check_call ls ls3 then Tau (mix_ilsteps lp (pc_between fn pcs pce) ls3)
                else Exception.throw ErrSemUndef)
    else Tau (mix_ilsteps lp (pc_between fn pcs pce) ls2)
  | Error e => Exception.throw e
  end.
Proof.
  rewrite {1}/mix_ilsteps while.unfold_while => C hfn hpc hsz h0Q.
  have -> : pc_between fn pcs pce ls.
  + by rewrite /pc_between hfn eqxx hpc.
  rewrite {1}/mix_ilstep /istep /is_call /step.
  rewrite (find_instr_skip0 C) => //.
  rewrite (onth_nth_size dummy_linstr) //.
  case: eval_instr => [ls2 | e] /=; last by rewrite !bind_throw; reflexivity.
  rewrite bind_ret_l; case: li_i => /= *;
   try by rewrite bind_ret_l; reflexivity.
  rewrite bind_bind; apply eqit_bind; first reflexivity.
  move=> ?; case: ifP => _.
  + rewrite bind_ret_l; reflexivity.
  rewrite bind_throw; reflexivity.
Qed.

Lemma step_mix_ilsteps fn P Q pcs pce ls  :
  is_linear_of lp fn (P ++ Q) ->
  lfn ls = fn -> lpc ls = size P ->
  pcs <= size P < pce ->
  0 < size Q ->
  mix_ilsteps lp (pc_between fn pcs pce) ls ≈
  match eval_instr lp (nth dummy_linstr Q 0) ls with
  | Ok ls2 =>
    if is_Lcall (li_i (nth dummy_linstr Q 0)) is Some fn' then
       ITree.bind (trigger_inl1 (mix_to_small_steps.Call fn' ls2))
        (λ ls3, if check_call ls ls3 then mix_ilsteps lp (pc_between fn pcs pce) ls3
                else Exception.throw ErrSemUndef)
    else mix_ilsteps lp (pc_between fn pcs pce) ls2
  | Error e => Exception.throw e
  end.
Proof.
  move=> C hfn hpc hsz h0Q; rewrite (step_mix_ilsteps_eq_itree C) //.
  case: eval_instr => [ls' | ?]; last reflexivity.
  case: is_Lcall; last by apply eqit_Tau_l; reflexivity.
  move=> fn'; apply eqit_bind; first reflexivity.
  move=> ls''; case: ifP => _; last reflexivity.
  by apply eqit_Tau_l; reflexivity.
Qed.

Lemma sem_fopns_args_mix_ilsteps fn P Q ii lc pcs pce ls :
  is_linear_of lp fn (P ++ map (li_of_fopn_args ii) lc ++ Q) ->
  lfn ls = fn ->
  lpc ls = size P ->
  pcs = size P ->
  pce = size P + size lc ->
  mix_ilsteps lp (pc_between fn pcs pce) ls ≈
    match sem_fopns_args (to_estate ls) lc with
    | Ok s' => Ret (of_estate s' fn pce)
    | Error err => Exception.throw err
    end.
Proof.
  move=> + ? + ??; subst fn pcs pce.
  elim: lc P ls => /= [ | [[xs o] es] lc hrec] P ls.
  + rewrite addn0 => _ <-; rewrite mix_ilsteps_0.
    + rewrite of_estate_to_estate; reflexivity.
    rewrite /pc_between /= eqxx; simpl_size; lia.
  rewrite /sem_fopn_args => C hpc.
  rewrite (step_mix_ilsteps C) //; last by simpl_size; lia.
  rewrite /eval_instr /=.
  rewrite -2!Let_Let.
  have -> : Let a := Let x := fexpr_sem.sem_rexprs (to_estate ls) es in exec_sopn o x in
            fexpr_sem.write_lexprs xs a (to_estate ls)
            =
            Let args := fexpr_sem.sem_rexprs (to_estate ls) es in
            (Let res := exec_sopn o args in fexpr_sem.write_lexprs xs res (to_estate ls)).
  + by rewrite !Let_Let.
  case: (Let _ := fexpr_sem.sem_rexprs _ _ in _) => [s1 | err] /=; last reflexivity.
  move: C; rewrite -addSnnS -cat_rcons => C.
  rewrite (mix_ilsteps_split (pcs' := (size P).+1) (pce' := (size P).+1 + size lc)) //.
  have := hrec _  (lnext_pc (lset_estate' ls s1)) C; rewrite size_rcons => ->; last first.
  + by rewrite /lnext_pc /= hpc.
  have -> : (to_estate (lnext_pc (lset_estate' ls s1))) = s1 by case: (s1).
  case: sem_fopns_args => [s2 | err]; last by rewrite bind_throw; reflexivity.
  rewrite bind_ret_l mix_ilsteps_b0 //; reflexivity.
Qed.

End WITH_PARAMS.
