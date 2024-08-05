From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import psem.
Import Utf8 Lia.
Import Memory low_memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

Context
  {wsw:WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Lemma write_lvals_write_lval wdb gd lv v s :
  write_lval wdb gd lv v s = write_lvals wdb gd s [:: lv ] [:: v ].
Proof. by rewrite /=; case: write_lval. Qed.

Lemma get_write_var_word wdb s s' ws (w : word ws) x :
  vtype (v_var x) = sword ws
  -> write_var wdb x (Vword w) s = ok s'
  -> (evm s').[v_var x] = Vword w.
Proof.
  by move=> hty /write_varP [-> _ _]; rewrite /= Vm.setP_eq /= hty cmp_le_refl !orbT.
Qed.

Lemma vrvs_Lvar xs :
  vrvs [seq Lvar x | x <- xs] = sv_of_list v_var xs.
Proof. rewrite /vrvs /sv_of_list; elim: xs Sv.empty => //=. Qed.

Lemma vrvs_to_lvals X (xs : seq X) f :
  Sv.Equal (vrvs (to_lvals (map f xs))) (sv_of_list f xs).
Proof.
  by rewrite /to_lvals map_comp vrvs_Lvar 2!sv_of_list_map sv_of_list_eq_ext.
Qed.

Lemma write_vars_eq_ex wdb xs vs s s' :
  write_vars wdb xs vs s = ok s' →
  evm s =[\ sv_of_list v_var xs] evm s' .
Proof.
  by rewrite (write_vars_lvals _ [::]) => /vrvsP; rewrite vrvs_Lvar.
Qed.

Lemma write_lvals_emem wdb gd xs ys s vs s' :
  mapM get_lvar xs = ok ys →
  write_lvals wdb gd s xs vs = ok s' →
  emem s' = emem s.
Proof.
  elim: xs ys vs s; first by move => _ [] // ? _ [] ->.
  move => x xs ih /=; t_xrbindP => _ [] // ???? X ? /ih{ih}ih _; t_xrbindP => ? Y /ih{ih}->.
  by case: x X Y => // x _; rewrite /= /write_var; t_xrbindP => ?? <-.
Qed.

Lemma write_lvals_escs wdb gd xs s vs s' :
  write_lvals wdb gd s xs vs = ok s' →
  escs s' = escs s.
Proof.
  elim: xs vs s => [ | x xs ih] /= [] // => [ _ [->] //| v vs s].
  by t_xrbindP => ? /lv_write_scsP -> /ih.
Qed.

(* sem_stack_stable and sem_validw_stable both for uprog and sprog *)
(* inspired by sem_one_varmap_facts *)

Lemma write_lval_stack_stable wdb gd x v s s' :
  write_lval wdb gd x v s = ok s' →
  stack_stable (emem s) (emem s').
Proof.
  case: x => [ vi ty | x | al ws x e | al aa ws x e | aa ws len x e ] /=.
  - by move=> /write_noneP [<-].
  - by move => /write_var_memP ->.
  - rewrite /=; t_xrbindP => ?????????? m' ok_m' <- /=.
    exact: write_mem_stable ok_m'.
  all: by apply: on_arr_varP; rewrite /write_var; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_stack_stable wdb gd xs vs s s' :
  write_lvals wdb gd s xs vs = ok s' →
  stack_stable (emem s) (emem s').
Proof.
  elim: xs vs s => [ | x xs ih ] [] //; first by move => ? [<-].
  by move => v vs s /=; t_xrbindP => ? /write_lval_stack_stable -> /ih.
Qed.

Lemma write_lval_validw wdb gd x v s s' :
  write_lval wdb gd x v s = ok s' ->
  validw (emem s) =3 validw (emem s').
Proof.
  case: x => [ vi ty | x | al ws x e | al aa ws x e | aa ws len x e ] /=.
  - by move => /write_noneP [] <-.
  - by move => /write_var_memP <-.
  - t_xrbindP => /= ?? ?? ?? ? ? ? ? ? h <- /=.
    by move=> ???; rewrite (write_validw_eq h).
  all: by apply: on_arr_varP; rewrite /write_var; t_xrbindP => ?????????????? <-.
Qed.

Lemma write_lvals_validw wdb gd xs vs s s' :
  write_lvals wdb gd s xs vs = ok s' ->
  validw (emem s) =3 validw (emem s').
Proof.
  elim: xs vs s.
  - by case => // ? [] ->.
  move => x xs ih [] // v vs s /=; t_xrbindP => ? /write_lval_validw h /ih.
  by move=> h1 al p ws; rewrite h h1.
Qed.

Lemma alloc_free_stack_stable m1 ws sz ioff sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz ioff sz' m2 ->
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

Lemma alloc_free_validw_stable m1 ws sz ioff sz' m2 m2' m3 :
  alloc_stack_spec m1 ws sz ioff sz' m2 ->
  stack_stable m2 m2' ->
  validw m2 =3 validw m2' ->
  free_stack_spec m2' m3 ->
  validw m1 =3 validw m3.
Proof.
  move=> hass hss hvalid hfss.
  move=> al p ws'.
  congr (_ && _).
  apply: all_ziota => i hi.
  rewrite !(valid8_validw _ Aligned).
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
  move: (ass_ioff hass) (ass_add_ioff hass); lia.
Qed.

Section MEM_EQUIV.

Context {pT: progT} {sCP: semCallParams}.

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
  move=> al p ws; transitivity (validw m2 al p ws).
  + exact: hvalid1.
  exact: hvalid2.
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
  move=> /dup[] /write_lvals_validw ho3 /write_lvals_stack_stable ?.
  split; [rewrite ho1 | move=> ???; rewrite ho2] => //; exact: ho3.
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
  move => ???????? /write_var_memP A _ B _ C; red.
  rewrite A; etransitivity; [ exact: B | exact: C ].
Qed.

Lemma mem_equiv_call : sem_Ind_call P ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vres _ _
    ? /dup[] /write_lvals_validw ? /write_lvals_stack_stable ?.
  red. etransitivity; by eauto.
Qed.

Lemma mem_equiv_proc : sem_Ind_proc P ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' ok_fd ok_vargs ok_s0 ok_s1 _ Hc _ _ -> ->.
  rewrite /Pc -(write_vars_memP ok_s1) in Hc.
  by apply (init_finalize_mem_equiv ok_s0 Hc).
Qed.

Lemma sem_mem_equiv s1 c s2 :
  sem P ev s1 c s2 → emem s1 ≡ emem s2.
Proof.
  exact:
    (sem_Ind
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
  exact:
    (sem_I_Ind
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
  exact:
    (sem_i_Ind
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
  exact:
    (sem_call_Ind
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
  sem p ev s1 c s2 → validw (emem s1) =3 validw (emem s2).
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
  sem_i p ev s1 c s2 → validw (emem s1) =3 validw (emem s2).
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
  sem_I p ev s1 c s2 → validw (emem s1) =3 validw (emem s2).
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
  sem_call p ev scs1 m1 fn vargs scs2 m2 vres -> validw m1 =3 validw m2.
Proof.
  apply sem_call_mem_equiv => {scs1 m1 fn vargs scs2 m2 vres}.
  by move=> s1 s2 m2 ef /= [<-].
Qed.

Lemma sem_stack_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem p gd s1 c s2 -> stack_stable (emem s1) (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_validw_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem p gd s1 c s2 -> validw (emem s1) =3 validw (emem s2).
Proof.
  apply sem_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
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
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_i_validw_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem_i p gd s1 c s2 -> validw (emem s1) =3 validw (emem s2).
Proof.
  apply sem_i_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
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
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_I_validw_stable_sprog (p : sprog) (gd : pointer) s1 c s2 :
  sem_I p gd s1 c s2 -> validw (emem s1) =3 validw (emem s2).
Proof.
  apply sem_I_mem_equiv => {s1 c s2}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
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
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

Lemma sem_call_validw_stable_sprog (p : sprog) (gd : pointer) scs1 m1 fn vargs scs2 m2 vres :
  sem_call p gd scs1 m1 fn vargs scs2 m2 vres ->
  validw m1 =3 validw m2.
Proof.
  apply sem_call_mem_equiv => {scs1 m1 fn vargs scs2 m2 vres}.
  move=> s1 s2 m2 ef /=; rewrite /init_stk_state /finalize_stk_mem.
  t_xrbindP=> m1 /Memory.alloc_stackP hass /=.
  do 2!rewrite write_var_eq_type //=; move=> [<-] /= [hss hvalid].
  have hfss := Memory.free_stackP m2.
  split.
  + by apply (alloc_free_stack_stable hass hss hfss).
  by apply (alloc_free_validw_stable hass hss hvalid).
Qed.

(** The semantics is deterministic. *)
Section DETERMINISM.

Context
  {pT: progT}
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
  red=> s1 scs2 m2 s2 xs fn args vargs vs ok_vargs _
    ih ok_s2 s2' /sem_iE[] ? [] ? [] ? [] ?[].
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
  exact:
    (sem_Ind
       sem_deter_nil
       sem_deter_cons
       sem_deter_mkI
       sem_deter_asgn
       sem_deter_opn
       sem_deter_syscall
       sem_deter_if_true
       sem_deter_if_false
       sem_deter_while_true
       sem_deter_while_false
       sem_deter_for
       sem_deter_for_nil
       sem_deter_for_cons
       sem_deter_call
       sem_deter_proc
       h).
Qed.

Lemma sem_i_deterministic s1 i s2 s2' :
  sem_i p ev s1 i s2 →
  sem_i p ev s1 i s2' →
  s2 = s2'.
Proof.
  move => h.
  exact:
    (sem_i_Ind
       sem_deter_nil
       sem_deter_cons
       sem_deter_mkI
       sem_deter_asgn
       sem_deter_opn
       sem_deter_syscall
       sem_deter_if_true
       sem_deter_if_false
       sem_deter_while_true
       sem_deter_while_false
       sem_deter_for
       sem_deter_for_nil
       sem_deter_for_cons
       sem_deter_call
       sem_deter_proc
       h).
Qed.

Lemma sem_call_deterministic scs1 m1 fn va scs2 m2 vr scs2' m2' vr' :
  sem_call p ev scs1 m1 fn va scs2 m2 vr →
  sem_call p ev scs1 m1 fn va scs2' m2' vr' →
  [/\ scs2 = scs2', m2 = m2' & vr = vr'].
Proof.
  move => h.
  exact:
    (sem_call_Ind
       sem_deter_nil
       sem_deter_cons
       sem_deter_mkI
       sem_deter_asgn
       sem_deter_opn
       sem_deter_syscall
       sem_deter_if_true
       sem_deter_if_false
       sem_deter_while_true
       sem_deter_while_false
       sem_deter_for
       sem_deter_for_nil
       sem_deter_for_cons
       sem_deter_call
       sem_deter_proc
       h).
Qed.

End DETERMINISM.

(* ------------------------------------------------------------------- *)
Lemma cast_wP wdb sz e gd s v :
  sem_pexpr wdb gd s (Papp1 (Oword_of_int sz) e) = ok v →
  exists2 v', sem_pexpr wdb gd s (cast_w sz e) = ok v' & value_uincl v v'.
Proof.
  elim: e v => /=; t_xrbindP => //.
  1, 2: by move => > ->; eauto.
  1, 2, 6: by move => > _ > -> /= ->; eauto.
  1: by move => > _ > -> /= -> > -> /= -> > /= -> /= -> ->; eauto.
  3: by move => > _ > _ > _ > -> /= -> > -> /= -> > -> /= -> /= -> ->; eauto.
  - case.
    7: case.
    1, 3-6, 8: by move => > _ > /= -> /= -> /= ->; eauto.
    + move => > _ >.
      case: ifP; last by move => _ /= -> /= -> /= ->; eauto.
      rewrite /sem_sop1; t_xrbindP => A -> /= ? /to_wordI[] ? [] ? [] -> /truncate_wordP[] B -> <- /=.
      t_xrbindP => ? <- <-; eexists; first reflexivity.
      rewrite -/(zero_extend sz _) zero_extend_idem //=.
      apply: word_uincl_zero_ext.
      exact: cmp_le_trans A B.
    rewrite /= /sem_sop1 /=.
    t_xrbindP => e ih > A > B ? > /to_intI h ?; subst; case: h => ?; subst.
    move: ih.
    rewrite A /= B => /(_ _ erefl)[] ? -> /value_uinclE[] ? [] ? [] -> /andP[] sz_le /eqP D.
    rewrite /= truncate_word_le // -D.
    eexists; first reflexivity.
    apply/andP; split; first exact: cmp_le_refl.
    by rewrite wopp_zero_extend // zero_extend_u wrepr_opp.
  case.
  all: try match goal with [ |- forall h : op_kind, _ ] => case end.
  all: try by move => > _ > _ > /= -> > -> /= -> /= ->; eauto.
  all: move => e1 ih1 e2 ih2 > h1 > h2.
  all: rewrite /sem_sop2; t_xrbindP => /= ? A ? B ? [] <- <-.
  all: move: ih1 ih2.
  all: rewrite h1 h2 /= /sem_sop1 /= A B /=.
  all: move => /(_ _ erefl) [] v1 -> /value_uinclE[] ? [] ? [] -> /andP[] le1 /eqP {} h1.
  all: move => /(_ _ erefl) [] v2 -> /value_uinclE[] ? [] ? [] -> /andP[] le2 /eqP {} h2.
  all: case => <- /=.
  all: rewrite /sem_sop2 /= !truncate_word_le // {le1 le2} -h1 -h2 /=.
  all: eexists; first reflexivity.
  all: apply/andP; split; first by auto.
  - by rewrite wadd_zero_extend // !zero_extend_u wrepr_add.
  - by rewrite wmul_zero_extend // !zero_extend_u wrepr_mul.
  by rewrite wsub_zero_extend // !zero_extend_u wrepr_sub.
Qed.

End WITH_PARAMS.
