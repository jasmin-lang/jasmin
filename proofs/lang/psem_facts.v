From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem.
Import Utf8.
Import Memory low_memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {spp : SemPexprParams asm_op syscall_state}.

Lemma write_var_emem x v s s' :
  write_var x v s = ok s' →
  emem s = emem s'.
Proof. by rewrite /write_var; t_xrbindP => vm _ <-; rewrite emem_with_vm. Qed.

Lemma write_vars_emem xs vs a z :
  write_vars xs vs a = ok z →
  emem a = emem z.
Proof.
  elim: xs vs a => [ | x xs ih ] [] //.
  - by move => a [<-].
  by move => v vs a /=; t_xrbindP => b /write_var_emem -> /ih.
Qed.

(* sem_stack_stable and sem_validw_stable both for uprog and sprog *)
(* inspired by sem_one_varmap_facts *)

Lemma write_lval_stack_stable gd x v s s' :
  write_lval gd x v s = ok s' →
  stack_stable (emem s) (emem s').
Proof.
  case: x => [ vi ty | x | ws x e | aa ws x e | aa ws len x e ].
  - apply: on_vuP; first by move => _ _ ->.
    by move => _; case: ifP => // _ [<-].
  - by move => /write_var_emem ->.
  - rewrite /=; t_xrbindP => ?????????? m' ok_m' <- /=.
    exact: write_mem_stable ok_m'.
  all: by apply: on_arr_varP; rewrite /write_var; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_stack_stable gd xs vs s s' :
  write_lvals gd s xs vs = ok s' →
  stack_stable (emem s) (emem s').
Proof.
  elim: xs vs s => [ | x xs ih ] [] //; first by move => ? [<-].
  by move => v vs s /=; t_xrbindP => ? /write_lval_stack_stable -> /ih.
Qed.

Lemma write_lval_validw gd x v s s' :
  write_lval gd x v s = ok s' ->
  validw (emem s) =2 validw (emem s').
Proof.
  case: x => /=.
  - by move => _ ty /write_noneP [] <-.
  - by move => x /write_var_emem <-.
  - t_xrbindP => /= ????? ?? ?? ? ? ? ? ? h <- /=.
    by move=> ??; rewrite (write_validw_eq h).
  - move => aa sz x e.
    by apply: on_arr_varP; rewrite /write_var; t_xrbindP => ?????????????? <-.
  move => aa sz ty x e.
  by apply: on_arr_varP; rewrite /write_var; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_validw gd xs vs s s' :
  write_lvals gd s xs vs = ok s' ->
  validw (emem s) =2 validw (emem s').
Proof.
  elim: xs vs s.
  - by case => // ? [] ->.
  move => x xs ih [] // v vs s /=; t_xrbindP => ? /write_lval_validw h /ih.
  by move=> h1 p ws; rewrite h h1.
Qed.

Lemma alloc_free_stack_stable m1 ws sz sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  stack_stable m2 m2' ->
  free_stack_spec m2' m3 ->
  stack_stable m1 m3.
Proof.
  move=> hass hss hfss.
  split.
  + by rewrite hfss.(fss_root) -hss.(ss_root) hass.(ass_root).
  + by rewrite hfss.(fss_limit) -hss.(ss_limit) hass.(ass_limit).
  by rewrite hfss.(fss_frames) -hss.(ss_frames) hass.(ass_frames).
Qed.

Lemma alloc_free_validw_stable m1 ws sz sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz sz' m2 ->
  stack_stable m2 m2' ->
  validw m2 =2 validw m2' ->
  free_stack_spec m2' m3 ->
  validw m1 =2 validw m3.
Proof.
  move=> hass hss hvalid hfss.
  move=> p ws'.
  congr (_ && _).
  apply: all_ziota => i hi.
  rewrite !valid8_validw.
  rewrite hfss.(fss_valid) -hvalid hass.(ass_valid).
  rewrite -(ss_top_stack hss) -(ss_top_stack (alloc_free_stack_stable hass hss hfss)).
  rewrite /pointer_range.
  have [L H] := ass_above_limit hass.
  case: (@andP (_ <=? _)%Z); rewrite !zify.
  - case => ptr_i_lo ptr_i_hi.
    rewrite andbF; apply/negbTE; apply: stack_region_is_free.
    split; last exact: ptr_i_hi.
    etransitivity; last exact: ptr_i_lo.
    exact: L.
  rewrite andbT => ptr_not_fresh.
  set X := (X in _ || X).
  suff /negbTE -> : ~~ X; first by rewrite orbF.
  subst X; rewrite !zify => - [].
  change (wsize_size U8) with 1%Z.
  move => ptr_i_lo ptr_i_hi.
  apply: ptr_not_fresh.
  split; first exact: ptr_i_lo.
  move: H ptr_i_hi; clear => n.
  by Lia.lia.
Qed.

Section MEM_EQUIV.

Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Infix "≡" := mem_equiv (at level 40).

Hypothesis init_finalize_mem_equiv : forall s1 s2 m2 ef,
  init_state ef P.(p_extra) ev s1 = ok s2 ->
  emem s2 ≡ m2 ->
  emem s1 ≡ finalize ef m2.

Instance mem_equiv_trans : Transitive mem_equiv.
Proof.
  move => m1 m2 m3 [hss1 hvalid1] [hss2 hvalid2].
  split; first by transitivity m2.
  by move=> p ws; transitivity (validw m2 p ws).
Qed.

Let Pc s1 (_: cmd) s2 : Prop := emem s1 ≡ emem s2.
Let Pi s1 (_: instr) s2 : Prop := emem s1 ≡ emem s2.
Let Pi_r s1 (_: instr_r) s2 : Prop := emem s1 ≡ emem s2.
Let Pfor (_: var_i) (_: seq Z) s1 (_: cmd) s2 : Prop := emem s1 ≡ emem s2.
Let Pfun (scs1:syscall_state) m1 (_: funname) (_: seq value) (scs2:syscall_state) m2 (_: seq value) : Prop := m1 ≡ m2.

Lemma mem_equiv_nil : sem_Ind_nil Pc.
Proof. by []. Qed.

Lemma mem_equiv_cons : sem_Ind_cons P ev Pc Pi.
Proof. by move => x y z i c _ xy _ yz; red; etransitivity; eassumption. Qed.

Lemma mem_equiv_mkI : sem_Ind_mkI P ev Pi_r Pi.
Proof. by []. Qed.

Lemma mem_equiv_assgn : sem_Ind_assgn P Pi_r.
Proof. by move => s1 s2 x tg ty e v v' ok_v ok_v' /dup[] /write_lval_validw ? /write_lval_stack_stable. Qed.

Lemma mem_equiv_opn : sem_Ind_opn P Pi_r.
Proof. by move => s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => ???? /dup[] /write_lvals_validw ? /write_lvals_stack_stable. Qed.

Lemma mem_equiv_syscall : sem_Ind_syscall P Pi_r.
Proof. 
  move => s1 scs m s2 o xs es ves vs hes h. 
  have [ho1 ho2]:= exec_syscallS h.  
  move=> /dup[] /write_lvals_validw ? /write_lvals_stack_stable ?.
  by split; [rewrite ho1 | move=> ??; rewrite ho2].
Qed.

Lemma mem_equiv_if_true : sem_Ind_if_true P ev Pc Pi_r.
Proof. by []. Qed.

Lemma mem_equiv_if_false : sem_Ind_if_false P ev Pc Pi_r.
Proof. by []. Qed.

Lemma mem_equiv_while_true : sem_Ind_while_true P ev Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 aa c e c' _ A _ _ B _ C; red.
  etransitivity; first exact: A.
  etransitivity; first exact: B.
  exact: C.
Qed.

Lemma mem_equiv_while_false : sem_Ind_while_false P ev Pc Pi_r.
Proof. by []. Qed.

Lemma mem_equiv_for : sem_Ind_for P ev Pi_r Pfor.
Proof. by []. Qed.

Lemma mem_equiv_for_nil : sem_Ind_for_nil Pfor.
Proof. by []. Qed.

Lemma mem_equiv_for_cons : sem_Ind_for_cons P ev Pc Pfor.
Proof.
  move => ???????? /write_var_emem A _ B _ C; red.
  rewrite A; etransitivity; [ exact: B | exact: C ].
Qed.

Lemma mem_equiv_call : sem_Ind_call P ev Pi_r Pfun.
Proof. move=> s1 scs2 m2 s2 ii xs fn args vargs vres _ _ ? /dup[] /write_lvals_validw ? /write_lvals_stack_stable ?; red; etransitivity; [|split]; eassumption. Qed.

Lemma mem_equiv_proc : sem_Ind_proc P ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' ok_fd ok_vargs ok_s0 ok_s1 _ Hc _ _ -> ->.
  rewrite /Pc -(write_vars_emem ok_s1) in Hc.
  by apply (init_finalize_mem_equiv ok_s0 Hc).
Qed.

Lemma sem_mem_equiv s1 c s2 :
  sem P ev s1 c s2 → emem s1 ≡ emem s2.
Proof.
  by apply
    (@sem_Ind _ _ _ _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
              mem_equiv_nil
              mem_equiv_cons
              mem_equiv_mkI
              mem_equiv_assgn
              mem_equiv_opn
              mem_equiv_syscall
              mem_equiv_if_true
              mem_equiv_if_false
              mem_equiv_while_true
              mem_equiv_while_false
              mem_equiv_for
              mem_equiv_for_nil
              mem_equiv_for_cons
              mem_equiv_call
              mem_equiv_proc).
Qed.

Lemma sem_I_mem_equiv s1 i s2 :
  sem_I P ev s1 i s2 → emem s1 ≡ emem s2.
Proof.
  by apply
    (@sem_I_Ind _ _ _ _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
                mem_equiv_nil
                mem_equiv_cons
                mem_equiv_mkI
                mem_equiv_assgn
                mem_equiv_opn
                mem_equiv_syscall
                mem_equiv_if_true
                mem_equiv_if_false
                mem_equiv_while_true
                mem_equiv_while_false
                mem_equiv_for
                mem_equiv_for_nil
                mem_equiv_for_cons
                mem_equiv_call
                mem_equiv_proc).
Qed.

Lemma sem_i_mem_equiv s1 i s2 :
  sem_i P ev s1 i s2 → emem s1 ≡ emem s2.
Proof.
  by apply
    (@sem_i_Ind _ _ _ _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
                mem_equiv_nil
                mem_equiv_cons
                mem_equiv_mkI
                mem_equiv_assgn
                mem_equiv_opn
                mem_equiv_syscall
                mem_equiv_if_true
                mem_equiv_if_false
                mem_equiv_while_true
                mem_equiv_while_false
                mem_equiv_for
                mem_equiv_for_nil
                mem_equiv_for_cons
                mem_equiv_call
                mem_equiv_proc).
Qed.

Lemma sem_call_mem_equiv scs1 m1 fn vargs scs2 m2 vres :
  sem_call P ev scs1 m1 fn vargs scs2 m2 vres → m1 ≡ m2.
Proof.
  by apply
    (@sem_call_Ind _ _ _ _ _ _ _ _ Pc Pi_r Pi Pfor Pfun
                   mem_equiv_nil
                   mem_equiv_cons
                   mem_equiv_mkI
                   mem_equiv_assgn
                   mem_equiv_opn
                   mem_equiv_syscall
                   mem_equiv_if_true
                   mem_equiv_if_false
                   mem_equiv_while_true
                   mem_equiv_while_false
                   mem_equiv_for
                   mem_equiv_for_nil
                   mem_equiv_for_cons
                   mem_equiv_call
                   mem_equiv_proc).
Qed.

End MEM_EQUIV.

Lemma sem_stack_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem p ev s1 c s2 -> stack_stable (emem s1) (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_validw_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem p ev s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_i_stack_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem_i p ev s1 c s2 → stack_stable (emem s1) (emem s2).
Proof.
  apply sem_i_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_i_validw_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem_i p ev s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_i_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_I_stack_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem_I p ev s1 c s2 → stack_stable (emem s1) (emem s2).
Proof.
  apply sem_I_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_I_validw_stable_uprog (p : uprog) (ev : unit) s1 c s2 :
  sem_I p ev s1 c s2 → validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_I_mem_equiv => {s1 c s2}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_call_stack_stable_uprog (p : uprog) (ev : unit) scs1 m1 fn vargs scs2 m2 vres :
  sem_call p ev scs1 m1 fn vargs scs2 m2 vres -> stack_stable m1 m2.
Proof.
  apply sem_call_mem_equiv => {scs1 m1 fn vargs scs2 m2 vres}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_call_validw_stable_uprog (p : uprog) (ev : unit) scs1 m1 fn vargs scs2 m2 vres :
  sem_call p ev scs1 m1 fn vargs scs2 m2 vres -> validw m1 =2 validw m2.
Proof.
  apply sem_call_mem_equiv => {scs1 m1 fn vargs scs2 m2 vres}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_stack_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem p gd s1 c s2 -> stack_stable (emem s1) (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_validw_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem p gd s1 c s2 -> validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_i_stack_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem_i p gd s1 c s2 -> stack_stable (emem s1) (emem s2).
Proof.
  apply sem_i_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_i_validw_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem_i p gd s1 c s2 -> validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_i_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_I_stack_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem_I p gd s1 c s2 -> stack_stable (emem s1) (emem s2).
Proof.
  apply sem_I_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_I_validw_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem_I p gd s1 c s2 -> validw (emem s1) =2 validw (emem s2).
Proof.
  apply sem_I_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_call_stack_stable_sprog (p : sprog) (gd : pointer) scs1 m1 fn vargs scs2 m2 vres :
  sem_call p gd scs1 m1 fn vargs scs2 m2 vres -> stack_stable m1 m2.
Proof.
  apply sem_call_mem_equiv => {scs1 m1 fn vargs scs2 m2 vres}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_call_validw_stable_sprog (p : sprog) (gd : pointer) scs1 m1 fn vargs scs2 m2 vres :
  sem_call p gd scs1 m1 fn vargs scs2 m2 vres ->
  validw m1 =2 validw m2.
Proof.
  apply sem_call_mem_equiv => {scs1 m1 fn vargs scs2 m2 vres}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

(** The semantics is deterministic. *)
Section DETERMINISM.

Context
  {T}
  {pT:progT T}
  {sCP : semCallParams}.
Variable p : prog.
Variable ev : extra_val_t.

Let Pc s1 c s2 :=
  ∀ s2', sem p ev s1 c s2' → s2 = s2'.

Let Pi s1 i s2 :=
  ∀ s2', sem_I p ev s1 i s2' → s2 = s2'.

Let Pi_r s1 i s2 :=
  ∀ s2', sem_i p ev s1 i s2' → s2 = s2'.

Let Pfor i r s1 c s2 :=
  ∀ s2', sem_for p ev i r s1 c s2' → s2 = s2'.

Let Pfun scs1 m1 fn args scs2 m2 res :=
  ∀ scs2' m2' res', sem_call p ev scs1 m1 fn args scs2' m2' res' → [/\ scs2 = scs2', m2 =  m2' & res = res'].

Local Lemma sem_deter_nil : sem_Ind_nil Pc.
Proof. by move => s s' /semE. Qed.

Local Lemma sem_deter_cons : sem_Ind_cons p ev Pc Pi.
Proof.
  move => x y z i c _ ihi _ ihc z' /semE[] y' [] /ihi <-.
  exact: ihc.
Qed.

Local Lemma sem_deter_mkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. by move => ii i s1 s2 _ ih s2' /sem_IE /ih. Qed.

Arguments ok_inj {_ _ _ _}.

Local Lemma sem_deter_asgn : sem_Ind_assgn p Pi_r.
Proof.
  red => s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 s2' /sem_iE[] w [] w' [].
  rewrite ok_v => /ok_inj <-.
  rewrite ok_v' => /ok_inj <-.
  by rewrite ok_s2 => /ok_inj.
Qed.

Local Lemma sem_deter_opn : sem_Ind_opn p Pi_r.
Proof.
  red => s1 s2 tg o xs es ok_s2 s2' /sem_iE.
  by rewrite ok_s2 => /ok_inj.
Qed.

Local Lemma sem_deter_syscall : sem_Ind_syscall p Pi_r.
Proof.
  red => s1 scs m s2 o xs es ves vs hes ho hw s2' /sem_iE [scs'] [m'] [ves'] [vs'] [].
  by rewrite hes => -[<-]; rewrite ho => -[<- <- <-]; rewrite hw => -[].
Qed.

Local Lemma sem_deter_if_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  red => s1 s2 e c1 c2 eval_e _ ih s2' /sem_iE[] b [].
  by rewrite eval_e => /ok_inj [] <- /ih.
Qed.

Local Lemma sem_deter_if_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  red => s1 s2 e c1 c2 eval_e _ ih s2' /sem_iE[] b [].
  by rewrite eval_e => /ok_inj [] <- /ih.
Qed.

Local Lemma sem_deter_while_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  red => s1 s2 s3 s4 a c1 e c2 _ ih1 eval_e _ ih2 _ ih s4' /sem_iE[] _ [] b [] /ih1 <-.
  by rewrite eval_e => /ok_inj [] <- [] _ [] /ih2 <- /ih.
Qed.

Local Lemma sem_deter_while_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  red => s1 s2 a c1 e c2 _ ih eval_e s2' /sem_iE[] _ [] b [] /ih <-.
  by rewrite eval_e => /ok_inj [] <-.
Qed.

Local Lemma sem_deter_for : sem_Ind_for p ev Pi_r Pfor.
Proof.
  red => s1 s2 i d lo hi c vlo vhi ok_vlo ok_vhi _ ih s2' /sem_iE[] vlo' [] vhi' [].
  rewrite ok_vlo => /ok_inj[] <-.
  rewrite ok_vhi => /ok_inj[] <-.
  exact: ih.
Qed.

Local Lemma sem_deter_for_nil : sem_Ind_for_nil Pfor.
Proof. by red => s i c s' /sem_forE. Qed.

Local Lemma sem_deter_for_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  red => s s1 s2 s' i w ws c ok_s1' _ ih1 _ ih2 s3' /sem_forE[] ? [] ? [].
  by rewrite ok_s1' => /ok_inj <- /ih1 <- /ih2.
Qed.

Local Lemma sem_deter_call : sem_Ind_call p ev Pi_r Pfun.
Proof.
  red => s1 scs2 m2 s2 ii xs fn args vargs vs ok_vargs _ ih ok_s2 s2' /sem_iE[] ? [] ? [] ? [] ?[].
  rewrite ok_vargs => /ok_inj <- /ih[] <- <- <-.
  rewrite ok_s2.
  exact: ok_inj.
Qed.

Local Lemma sem_deter_proc : sem_Ind_proc p ev Pc Pfun.
Proof.
  red => scs1 m1 scs2 m2 fn fd va va' s1 s2 s3 vr vr' ok_fd ok_va ok_s1 ok_s2 _ ih ok_vr ok_vr' -> -> scs3 m3 vres h.
  have := sem_callE h; move=> [] ? [].
  rewrite ok_fd => /Some_inj <- [] ? [] ? [] ? [] ? [] ? [].
  rewrite ok_va => /ok_inj <- [].
  rewrite ok_s1 => /ok_inj <-.
  rewrite ok_s2 => /ok_inj <- /ih <- [].
  rewrite ok_vr => /ok_inj <-.
  by rewrite ok_vr' => /ok_inj <- [] -> ->.
Qed.

Lemma sem_deterministic s1 c s2 s2' :
  sem p ev s1 c s2 →
  sem p ev s1 c s2' →
  s2 = s2'.
Proof.
  move => h.
  exact: (@sem_Ind _ _ _ T pT sCP p ev Pc Pi_r Pi Pfor Pfun sem_deter_nil sem_deter_cons sem_deter_mkI sem_deter_asgn sem_deter_opn sem_deter_syscall sem_deter_if_true sem_deter_if_false sem_deter_while_true sem_deter_while_false sem_deter_for sem_deter_for_nil sem_deter_for_cons sem_deter_call sem_deter_proc _ _ _ h _).
Qed.

Lemma sem_i_deterministic s1 i s2 s2' :
  sem_i p ev s1 i s2 →
  sem_i p ev s1 i s2' →
  s2 = s2'.
Proof.
  move => h.
  exact: (@sem_i_Ind _ _ _ T pT sCP p ev Pc Pi_r Pi Pfor Pfun sem_deter_nil sem_deter_cons sem_deter_mkI sem_deter_asgn sem_deter_opn sem_deter_syscall sem_deter_if_true sem_deter_if_false sem_deter_while_true sem_deter_while_false sem_deter_for sem_deter_for_nil sem_deter_for_cons sem_deter_call sem_deter_proc _ _ _ h _).
Qed.

Lemma sem_call_deterministic scs1 m1 fn va scs2 m2 vr scs2' m2' vr' :
  sem_call p ev scs1 m1 fn va scs2 m2 vr →
  sem_call p ev scs1 m1 fn va scs2' m2' vr' →
  [/\ scs2 = scs2', m2 = m2' & vr = vr'].
Proof.
  move => h.
  exact: (@sem_call_Ind _ _ _ T pT sCP p ev Pc Pi_r Pi Pfor Pfun sem_deter_nil sem_deter_cons sem_deter_mkI sem_deter_asgn sem_deter_opn sem_deter_syscall sem_deter_if_true sem_deter_if_false sem_deter_while_true sem_deter_while_false sem_deter_for sem_deter_for_nil sem_deter_for_cons sem_deter_call sem_deter_proc _ _ _ _ _ _ _ h).
Qed.

End DETERMINISM.

End WITH_PARAMS.

(* TODO: move? *)
Lemma pword_of_wordE (ws : wsize) (w : word ws) p :
  {| pw_size := ws; pw_word := w; pw_proof := p; |} = pword_of_word w.
Proof.
  by rewrite (Eqdep_dec.UIP_dec Bool.bool_dec p (cmp_le_refl _)).
Qed.
