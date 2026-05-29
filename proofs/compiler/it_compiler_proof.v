From Coq Require Import Lia Uint63.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import fintype finfun ssralg.
From ITree Require Import
  Basics
  ITree
  ITreeFacts
.

Require Import
  arch_params_proof
  compiler
  compiler_util
  psem
  psem_facts
  core_logics
  relational_logic
  sem_one_varmap
  linear
  linear_sem
  it_sems_one_varmap
.
Require Import
  allocation_proof
  lower_spill_proof
  load_constants_in_cond_proof
  inline_proof
  insert_renaming_proof
  dead_calls_proof
  makeReferenceArguments_proof
  array_copy
  array_copy_proof
  array_init_proof
  unrolling_proof
  constant_prop_proof
  propagate_inline_proof
  dead_code_proof
  array_expansion
  array_expansion_proof
  remove_assert_proof
  remove_globals_proof
  stack_alloc_proof_2
  tunneling_proof
  tunneling_proof_2
  linearization_proof
  it_linearization_proof
  it_merge_varmaps_proof
  psem_of_sem_proof
  slh_lowering_proof
  direct_call_proof
  stack_zeroization_proof
  wint_word_proof
.

Require Import compiler_proof.

Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen_proof
  sem_params_of_arch_extra.

Require Import  asm_invariant .

Require Import hoare_valid.
Require Import xrutt xrutt_facts.

Definition values_uincl := List.Forall2 value_uincl.

Section IT.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {sc_sem : syscall.syscall_sem syscall_state}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {it_asm_scsem : it_asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
.

Notation E := (ErrEvent +' RndEvent syscall_state) (only parsing).
Notation E0 := (RndEvent syscall_state) (only parsing).

#[local]
Instance wE : with_Error E E0 :=
  {|
    mfun1 := fun _ x => x;
    mfun2 := fun _ x => x;
    mid12 := fun _ x => erefl;
    mid21 := fun _ x => erefl;
  |}.

Definition isem_unit
  (p : uprog)
  (fn : funname)
  (fs : fstate) :
  itree E fstate :=
  it_sems_core.isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (wa := withassert)
    (sip := sip_of_asm_e)
    (scP := sCP_unit)
    (wE := wE)
    (rE := rndE)
    (wsw := nosubword)
    (dc := indirect_c)
    (pT := progUnit)
    p tt fn fs.

Definition isem_stack
  (sp : sprog)
  (rip : pointer)
  (fn : funname)
  (fs : fstate) :
  itree E fstate :=
  it_sems_core.isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (wa := noassert)
    (sip := sip_of_asm_e)
    (scP := sCP_stack)
    (wE := wE)
    (rE := rndE)
    (wsw := withsubword)
    (dc := direct_c)
    (pT := progStack)
    sp rip fn fs.

Definition isem_linear (lp : lprog) :=
  ilsem_exportcall lp (wE := wE) (rE := rndE).

Definition isem_asm (xp : asm_prog) :=
  iasmsem_exportcall
    (asm_d := _asm)
    (call_conv := call_conv)
    (asm_scsem := asm_scsem)
    (wE := wE)
    (rE := rndE)
    xp.

Definition RndPre (A B : Type) : E0 A -> E0 B -> Prop :=
  fun '(Rnd scs1 n1) '(Rnd scs2 n2) => scs1 = scs2 /\ n1 = n2.

Definition RndPost (A B : Type) : E0 A -> A -> E0 B -> B -> Prop :=
  fun '(Rnd scs1 n1) a '(Rnd scs2 n2) b => a = b.

#[local]
Instance HandlerContract : EventRels E0 :=
  {|
    EPreRel0_ := RndPre;
    EPostRel0_ := RndPost;
  |}.

#[local]
Instance RndE00 : RndE0 syscall_state (RndEvent syscall_state) := fun T => id.

#[local]
Instance RndE0Refl : RndE0_refl HandlerContract.
Proof. by constructor. Qed.

#[local]
Instance HandlerContract_trans :
  EventRels_trans HandlerContract HandlerContract HandlerContract.
Proof.
constructor.
- by move => T1 T2 T3 [scs1 n1] [scs2 n2] [scs3 n3] [-> ->] [-> ->].
by move => ??? [??] [??] [??] ?? [] -> -> [] -> -> -> /=; eauto.
Qed.

Section FIRST_PART.

#[local] Existing Instance withsubword.
#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Lemma it_inliningP {to_keep p p' ev fn} :
  fn \in to_keep ->
  inlining cparams to_keep p = ok p' ->
  wiequiv_f (dc1 := indirect_c) (dc2 := indirect_c)
    p p' ev ev pre_incl fn fn post_incl.
Proof.
rewrite /inlining; t_xrbindP=> hfn p0 hp0 p1.
rewrite !print_uprogP => hp1 ?; subst p'.
apply: wiequiv_f_trans_UU_UU; first exact: it_inline_call_errP hp0.
apply: it_sem_refl_EE_UU; exact: (it_dead_calls_err_seqP hp1 _ hfn).
Qed.

Lemma it_postprocessP {dc : DirectCall} (p p' : uprog) fn ev :
  dead_code_prog (ap_is_move_op aparams) (const_prop_prog p) false = ok p' ->
  wiequiv_f (dc1 := dc) (dc2 := dc)
    p p' ev ev pre_incl fn fn post_incl.
Proof.
move=> hp'.
apply: wiequiv_f_trans_UU_UU; first exact: it_const_prop_callP.
apply: it_sem_refl_EU_UU.
exact: (it_dead_code_callPu (hap_is_move_opP haparams) ev hp' (fn := fn)).
Qed.

Lemma it_unrollP {dc : DirectCall} (fn : funname) (p p' : prog) ev :
  unroll_loop (ap_is_move_op aparams) p = ok p' ->
  wiequiv_f (dc1 := dc) (dc2 := dc)
    p p' ev ev pre_incl fn fn post_incl.
Proof.
rewrite /unroll_loop; t_xrbindP; elim: loop_counter p => [// | n hind] /= p pu hpu.
case hu: unroll_prog => [pu' []]; last first.
- move=> [<-]; exact: it_postprocessP hpu.
move: hu; rewrite (surjective_pairing (unroll_prog pu)) => -[? _]; subst pu'.
t_xrbindP=> p0 hp0 hp'.
apply: wiequiv_f_trans_UU_UU; last exact: hind hp0 hp'.
apply: wiequiv_f_trans_UU_UU; first exact: it_postprocessP hpu.
apply: it_sem_refl_EE_UU; exact: it_unroll_callP.
Qed.

Lemma it_live_range_splittingP {dc : DirectCall} (p p': uprog) fn ev :
  live_range_splitting aparams cparams p = ok p' ->
  wiequiv_f (dc1 := dc) (dc2 := dc)
    p p' ev ev pre_eq fn fn post_incl.
Proof.
rewrite /live_range_splitting; t_xrbindP.
rewrite !print_uprogP => ok_p' pa ok_pa; rewrite print_uprogP => ?; subst pa.
move: p ok_p' ok_pa => [fs gd ep] /= ok_p' ok_pa.
apply: wiequiv_f_trans_UU_EU; first exact: (it_alloc_call_uprogP _ _ ok_p').
apply: (
  wkequiv_io_weaken
    (P := pre_incl fn fn)
    (Q := post_incl fn fn)
) => //.
- move=> ? _ [_ <-]; split=> //; split=> //; exact: values_uincl_refl.
apply: it_sem_refl_EU_UU.
exact: (it_dead_code_callPu (hap_is_move_opP haparams) ev ok_pa (fn := fn)).
Qed.

Lemma it_compiler_first_part {entries p p' ev fn} :
  compiler_first_part aparams cparams entries p = ok p' ->
  fn \in entries ->
  wiequiv_f
    (wa1 := withassert) (wa2 := noassert)
    (wsw1 := nosubword) (wsw2 := withsubword)
    (dc1 := indirect_c) (dc2 := direct_c)
    p p' ev ev pre_eq fn fn post_incl.
Proof.
rewrite /compiler_first_part; t_xrbindP => paw.
rewrite print_uprogP => ok_paw pa0.
rewrite !print_uprogP => ok_pa0 pb.
rewrite print_uprogP => ok_pb pa ok_pa pc ok_pc ok_puc ok_puc'.
rewrite !print_uprogP => pd ok_pd.
rewrite !print_uprogP => pe ok_pe.
rewrite !print_uprogP => pf ok_pf.
rewrite !print_uprogP => pg ok_pg.
rewrite !print_uprogP => ph ok_ph pi ok_pi.
rewrite !print_uprogP => plc ok_plc.
rewrite !print_uprogP => ok_fvars pj ok_pj pp.
rewrite !print_uprogP => ok_pp <- {p'} ok_fn.

apply: (wiequiv_f_trans_EE_EU (wsw2:=nosubword) (dc2:=indirect_c)).
+ by apply: (it_remove_assert_progP
  (dc := indirect_c) (sip := sip_of_asm_e) (pT := progUnit)
  (wsw := nosubword) ev).

apply: (wiequiv_f_trans_EE_EU (wsw2:= withsubword) (dc2:=indirect_c)).
+ exact: it_psem_call_u.

apply: wiequiv_f_trans_UU_EU; first exact (it_wi2w_progP _ _ ok_paw).
apply: wiequiv_f_trans_UU_EU;
  first exact: (it_insert_renaming_callP (insert_renaming cparams)).
apply: wiequiv_f_trans_UU_EU; first exact: (it_array_copy_fdP _ ok_pa0).
apply: wiequiv_f_trans_EE_EU; first exact: it_add_init_callP.
apply: wiequiv_f_trans_EE_EU; first exact: (it_lower_spill_fdP _ ok_pb).
apply: wiequiv_f_trans_UU_EU.
apply: [elaborate it_inliningP (ev := ev) ok_fn ok_pa ].
apply: wiequiv_f_trans_UU_EU; first exact: it_unrollP ok_pc.
apply: wiequiv_f_trans_EE_EU;
  first exact: (it_dead_calls_err_seqP ok_pd _ ok_fn).
apply: wiequiv_f_trans_EU_EU; first exact: it_live_range_splittingP ok_pe.
apply: wiequiv_f_trans_UU_EU; first exact: (it_remove_init_fdPu is_reg_array).
apply: wiequiv_f_trans_EE_EU.
- apply: (wkequiv_io_weaken (P := rpreF (eS := mra_spec _) fn fn)) => //;
    last exact: (it_makeReferenceArguments_callP _ ok_pf).
  by move=> ???? [_ <-] [<-].
apply: wiequiv_f_trans_UU_EU; first exact: it_indirect_to_direct.
apply: wiequiv_f_trans_EE_EU; first exact: (it_expand_callP ok_pg ok_fn).
apply: wiequiv_f_trans_EU_EU; first exact: it_live_range_splittingP ok_ph.
apply: wiequiv_f_trans_EU_EU; first exact: RGP.it_remove_globP ok_pi.
apply: wiequiv_f_trans_EE_EU; first exact: (it_load_constants_progP ok_plc).
apply: wiequiv_f_trans_EE_EU;
  first exact: (hlop_it_lower_callP
    (hap_hlop haparams) (lowering_opt cparams) (warning cparams) ok_fvars).
apply: wiequiv_f_trans_UU_EU; first exact: (it_pi_callP _ ok_pj).
apply: wiequiv_f_trans_EE_EU;
  first exact: (it_lower_call_export (hap_hshp haparams) _ ok_pp ok_fn).

apply: wkequiv_io_weaken; last exact: wiequiv_f_eq.
1-3: done.
move=> ???? [_ <-] <-; split=> //; exact: values_uincl_refl.
Qed.

End FIRST_PART.

Section THIRD_PART.

Context
  {entries : seq funname}
  {p p' : sprog}
  {ev : pointer}
.

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

Let rminfo (rp : funname -> option (seq (option nat))) fn :=
  match rp fn with
  | Some l =>
      let l' := map (fun i => if i is None then true else false) l in
      if all (fun b => b) l' then None else Some l' (* do we want that? *)
  | None => removereturn cparams p fn
  end.

Definition post_dc rp := rpostF (eS := dc_spec (rminfo rp)).

Lemma fn_keep_only_uincl rm fn vs1 vs2 vs3 :
  values_uincl vs1 vs2 ->
  values_uincl (fn_keep_only rm fn vs2) vs3 ->
  values_uincl (fn_keep_only rm fn vs1) vs3.
Proof.
rewrite /fn_keep_only; case: rm => [tk|]; last exact: values_uincl_trans.
elim: tk vs1 vs2 vs3 => [|[] tk hind] vs1 vs2 vs3 /=;
  first (exact: values_uincl_trans);
  case: vs2 vs1 => [|v2 vs2] [|v1 vs1] /List_Forall2_inv //= [h hs];
  last exact: hind.
case: vs3 => [|v3 vs3] /List_Forall2_inv //= [h' hs'].
constructor; first exact: (value_uincl_trans h h').
exact: (hind _ _ _ hs hs').
Qed.

Lemma it_compiler_third_part {rp fn} :
  compiler_third_part aparams cparams rp p = ok p' ->
  wiequiv_f (scP1 := sCP_stack) (scP2 := sCP_stack)
    p p' ev ev pre_eq fn fn (post_dc rp).
Proof.
rewrite /compiler_third_part; t_xrbindP=> pa ok_pa.
rewrite !print_sprogP.
set pb := {| p_funcs := regalloc _ _; |} => ok_pb pc ok_p'.
rewrite print_sprogP => ?; subst pc.
apply: (
  wiequiv_f_trans
    (scP1 := sCP_stack) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_eq) (rpostF23 := post_incl)
    _ _
    (it_dead_code_tokeep_callPs
       (sip := sip_of_asm_e) (hap_is_move_opP haparams) _ ok_pa)
).
- exact: rpreF_trans_eq_eq_eq.
- move=> s1 s2 _ r1 r3 _ [_ <-] [r2 [?? hvals2] [?? hvals3]].
  split; only 1,2: congruence.
  exact: values_uincl_trans hvals2 hvals3.
rewrite -{1}(surj_prog (pT := progStack) pa).
apply: (
  wiequiv_f_trans
    (scP1 := sCP_stack) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_eq) (rpostF23 := post_incl)
    _ _
    (it_alloc_callP_sprogP _ _ ok_pb (fn:= fn))
).
- exact: rpreF_trans_eq_uincl_eq.
- exact: rpostF_trans_uincl_eq_uincl_uincl.
apply: (
  wiequiv_f_trans
    (scP1 := sCP_stack) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_incl) (rpostF23 := post_incl)
    _ _
    (it_dead_code_callPs
       (sip := sip_of_asm_e) (hap_is_move_opP haparams) _ ok_p')
       ).
- move=> s1 s2 [_ <-]; exists s1 => //; split=> //; exact: fs_uinclR.
- move=> s1 _ s3 r1 r3 [_ <-] _ [r2 [?? hvals2] [?? hvals3]].
  split; only 1,2: congruence.
  exact: values_uincl_trans hvals2 hvals3.
exact: (it_sem_uincl_f (sCP := sCP_stack) p' ev (fn := fn)).
Qed.

End THIRD_PART.

Section FRONT_END.

Context
  (entries : seq funname)
  (up : uprog (asmop := _asmop))
  (sp : sprog (pd := _pd) (asmop := _asmop))
  (rip : pointer)
.

Definition wf_args_s fn ms mt vs vt :=
  wf_args
    (size_glob sp) rip ms mt (get_wptrs up fn) (get_align_args sp fn) vs vt.

Definition it_extend_mem ms mt := extend_mem ms mt rip (sp_globs (p_extra sp)).

Definition front_end_pre : relPreF :=
  fun fn fn' s t =>
    let: args := fvals s in
    let: argt := fvals t in
    let: ms := fmem s in
    let: mt := fmem t in
    [/\ fn = fn'
      , alloc_ok sp fn mt
      , wf_args_s fn ms mt args argt
      , Forall3 (value_eq_or_in_mem mt) (get_wptrs up fn) args argt
      , it_extend_mem ms mt
      & fscs s = fscs t
    ].

Definition front_end_post : relPostF :=
  fun fn _ s t s' t' =>
    let: args := fvals s in
    let: argt := fvals t in
    let: ms := fmem s in
    let: mt := fmem t in
    let: ress := fvals s' in
    let: rest := fvals t' in
    let: ms' := fmem s' in
    let: mt' := fmem t' in
    let: n := get_nb_wptr up fn in
    [/\ List.Forall2 (value_in_mem mt') (take n ress) (take n argt)
      , values_uincl (drop n ress) rest
      , it_extend_mem ms' mt'
      , mem_unchanged_params ms mt mt' (get_wptrs up fn) args argt
      & fscs s' = fscs t'
    ].

#[local]
Instance FrontEndEquiv : EquivSpec :=
  {|
    rpreF_ := front_end_pre;
    rpostF_ := front_end_post;
  |}.

Lemma it_compiler_front_endP {ev fn} :
  compiler_front_end aparams cparams entries up = ok sp ->
  fn \in entries ->
  wiequiv_f
    (wsw1 := nosubword) (wsw2 := withsubword)
    (wa1 := withassert) (wa2 := noassert)
    (dc1 := indirect_c) (dc2 := direct_c)
    up sp ev rip rpreF fn fn rpostF.
Proof.
rewrite /compiler_front_end; t_xrbindP=> p1 ok_p1 check_p1 p2 ok_p2 p3.
rewrite print_sprogP => ok_p3 p4.
set rp := fun (fn : funname) => _.
rewrite print_sprogP => ok_sp ? ok_fn; subst p4.
apply: (wequiv_fun_get (scP1 := sCP_unit) (scP2 := sCP_stack)) => /= fd get_fd.

have [mglob ok_mglob] := [elaborate alloc_prog_get_fundef ok_p2 ].
have [_ p2_p3_extra] :=
  hlap_lower_address_prog_invariants (hap_hlap haparams) ok_p3.
have sp_p3_extra := [elaborate compiler_third_part_meta print_sprogP ok_sp ].
have p2_p1_extra := [elaborate alloc_prog_sp_globs ok_p2 ].
have [] := check_wf_ptrP check_p1 ok_fn get_fd.
set n := find _ _.
rewrite /= all2_map -eqseq_all => /eqP check_params check_return h.

apply: (
  wiequiv_f_trans
    (scP1 := sCP_unit) (scP2 := sCP_unit) (scP3 := sCP_stack)
    (rpreF23 := front_end_pre) (rpostF23 := front_end_post)
    _ _
    (it_compiler_first_part ok_p1 ok_fn)
).
- move=> s1 ? [? _]; by exists s1.
- move=> s1 _ s3 r1 r3 [_ <-] [_ halloc hwf hptr hmem hscs] [] r2
    [hscs1 hmem1 hval1] [] hptr' hres hmem' hparams hscs'.
  split=> //.
  + apply: Forall2_trans hptr'; first exact: value_uincl_value_in_mem_trans.
    exact: (Forall2_take hval1).
  + apply: Forall2_trans hres; first exact: value_uincl_trans.
    exact: (Forall2_drop hval1).
  + congruence.
  congruence.

apply: (wequiv_fun_get (scP1 := sCP_unit) (scP2 := sCP_stack)) => /= fd1
  get_fd1.
move: h => /(_ _ _ get_fd1)[] fd2 /[dup] ok_fd2 h get_fd2.
have [fd3 get_fd3 [_ _ _ _ _ fd2_fd3_extra]] :=
  hlap_lower_address_fd_invariants (hap_hlap haparams) ok_p3 get_fd2.
have [fd4 [get_fd4 fd3_fd4_align]] :=
  compiler_third_part_invariants print_sprogP ok_sp get_fd3.

apply: (
  wiequiv_f_trans
    (scP1 := sCP_unit) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_eq) (rpostF23 := post_dc (p := p3) rp)
    (p2 := p2) (ev2 := rip) (fn2 := fn)
    _ _
    (it_alloc_progP
       (hap_hshp haparams) (hap_hsap haparams) (hap_is_move_opP haparams)
       ok_p2 ev (rip := rip))
).
- move=> s1 s3 [] [_ hok hwf hptr hmem hscs] _; exists s3 => //; split=> //.
  + by rewrite -p2_p1_extra p2_p3_extra -sp_p3_extra.
  + move: hwf; rewrite /wf_args_s /get_wptrs get_fd /= check_params.
    rewrite /size_glob sp_p3_extra -p2_p3_extra p2_p1_extra.
    rewrite /get_align_args get_fd4 /= -fd3_fd4_align -fd2_fd3_extra.
    move: ok_fd2; rewrite /alloc_fd; by t_xrbindP=> _ _ <- /=.
  + move: hptr; rewrite /get_wptrs get_fd /=.
    apply: value_eq_or_in_mem_any_option.
    rewrite check_params.
    have /Forall2_flip :=
      map_Forall2 (omap pp_writable)
        (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)).
    apply Forall2_impl.
    by move=> _ ? <-; apply isSome_omap.
  + rewrite /alloc_ok get_fd2 => _ [<-].
    have :=
      compiler_third_part_alloc_ok haparams print_sprogP ok_sp hok get_fd3.
    by rewrite -fd2_fd3_extra.
- move=> s1 s2 _ r1 r3 [hscs_s1] hmem_s1 hwf_s1 heqinmem halloc [_ <-] [].
  move=> r2 [hscs1 m'_mi' vr2_wf vr2_eqinmem U] [hscs2 hmem2 vr_vr1].
  set rminfo := fun fn => _ in vr_vr1.
  set va := fvals s1.
  set va' := fvals s2.
  set vr := fvals r1.
  set vr1 := fvals r1.
  set vr2 := fvals r2.
  set m := fmem s1.
  set mi := fmem s2.
  set m' := fmem s1.
  set mi' := fmem r2.
  have hle1: n <= size fd.(f_params) by apply find_size.
  have [/esym size_vr1 /esym size_vr2] := Forall3_size vr2_wf.
  have [/esym size_va /esym size_va'] := Forall3_size heqinmem.
  have /(f_equal size) := check_params; rewrite 2!size_map => /esym size_sao_params.
  have hle2: n <= size vr.
  * have /(f_equal size) := check_return.
    rewrite size_cat size_map size_iota -size_vr1 => ->.
    exact: leq_addr.

  (* [vr2_eqinmem] can be split into two thanks to [check_results]:
     - the first [n] elements satisfy [value_in_mem];
     - the other ones satisfy equality. *)
  have [vr2_inmem vr2_eq]:
    List.Forall2 (value_in_mem mi') (take n vr) (take n vr2) /\
      drop n vr1 = drop n vr2.
  + split.
    + apply (nth_Forall2 (Vbool true) (Vbool true)).
      + by rewrite (size_takel hle2) size_takel // size_vr2 -size_vr1.
      rewrite (size_takel hle2) => i hi.
      rewrite nth_take // nth_take //.
      have := Forall3_nth vr2_eqinmem None (Vbool true) (Vbool true).
      rewrite -size_vr1 => /(_ _ (leq_trans hi hle2)).
      rewrite check_return nth_cat size_map size_iota hi (nth_map 0);
        last by rewrite size_iota.
      rewrite nth_iota // hmem2 /=.
    apply (eq_from_nth (x0 := Vbool true)).
    + by rewrite 2!size_drop size_vr1 size_vr2.
    move=> i; rewrite size_drop ltn_subRL => hi.
    rewrite 2!nth_drop.
    have := Forall3_nth vr2_eqinmem None (Vbool true) (Vbool true).
    rewrite -size_vr1 => /(_ _ hi).
    rewrite check_return nth_cat size_map size_iota lt_nm_n.
    by rewrite nth_nseq (ltn_sub2rE _ (leq_addr _ _)) -size_vr1 hi.

    (* [vr2_wf] can be rewritten into an equality thanks to [check_results] *)
    have {}vr2_wf: take n vr2 = take n va'.
    + apply (eq_from_nth (x0 := Vbool true)).
    + rewrite size_takel; last by rewrite size_vr2 -size_vr1.
      rewrite size_takel; last by rewrite size_va' size_sao_params.
      reflexivity.
    rewrite size_takel; last by rewrite size_vr2 -size_vr1.
    move=> i hi.
    rewrite nth_take // nth_take //.
    have := Forall3_nth vr2_wf None (Vbool true) (Vbool true).
    rewrite -size_vr1 => /(_ _ (leq_trans hi hle2)).
    rewrite check_return nth_cat size_map size_iota hi (nth_map 0);
      last by rewrite size_iota.
    by rewrite nth_iota //; case.

    (* [fn_keep_only rminfo fn] is just [drop] thanks to [check_results] *)
    have rminfo_vr2: fn_keep_only rminfo fn vr2 = drop n vr2.
    + rewrite /fn_keep_only /rminfo /rp ok_fn.
      set k := size (sao_return (ao_stack_alloc (stackalloc cparams p1) fn)).
      have ->:
        [seq match i with
           | Some _ => false
           | None => true
           end
        | i <- sao_return (ao_stack_alloc (stackalloc cparams p1) fn)]
           = nseq n false ++ nseq (k - n) true.
    + rewrite check_return map_cat.
      apply f_equal2.
    + by rewrite -map_comp map_const_nseq size_iota.
      by apply map_nseq.
      case heq: all.
    + by case: (n) heq => [|//] _; rewrite drop0.
      rewrite -{1}(cat_take_drop n vr2).
      rewrite keep_only_cat; last first.
    + rewrite size_takel; last by rewrite size_vr2 -size_vr1.
      by rewrite size_nseq.
      rewrite keep_only_false; last first.
    + by rewrite size_take; apply geq_minl.
      by rewrite keep_only_true.

  have hn : get_nb_wptr up fn = n.
  - by rewrite /get_nb_wptr /get_wptrs /= get_fd seq.find_map.

  split; last congruence.
  - rewrite hn -vr2_wf -hmem2; exact: vr2_inmem.
  - rewrite hn vr2_eq -rminfo_vr2; exact: vr_vr1.
  - by rewrite -hmem2 /it_extend_mem sp_p3_extra -p2_p3_extra p2_p1_extra.
  by rewrite /get_wptrs get_fd /= check_params -hmem2.

apply: (
  wiequiv_f_trans
    _ _
    (hlap_it_lower_addressP (hap_hlap haparams) ok_p3)
    (it_compiler_third_part ok_sp)
).
- exact: rpreF_trans_eq_eq_eq.
by move=> s1 _ _ r1 r3 [_ <-] [_ <-] [_ <-] [hscs hmem] h'.
Qed.

End FRONT_END.

Section BACK_END.

Context
  (entries : seq funname)
  (sp : sprog (pd := @_pd _ ep_of_asm_e) (asmop := @_asmop _ _ sip_of_asm_e))
  (tp : lprog (asmop := @_asmop _ _ sip_of_asm_e))
  (rip : pointer)
  (rsp_in_callee_saved : Sv.In (vid sp.(p_extra).(sp_rsp)) one_varmap.callee_saved)
.

#[local] Existing Instance withsubword.

Definition zeroized_p (ms mt mt' : mem) (p : pointer) : Prop :=
  ~~ validw ms Aligned p U8 ->
  [\/ read mt' Aligned p U8 = read mt Aligned p U8
    | read mt' Aligned p U8 = ok 0%R
  ].

Definition zeroized_s fn ms mt mt' :=
  cparams.(stack_zero_info) fn <> None ->
  forall p, zeroized_p ms mt mt' p.

Definition lget_vars (xs : seq var_i) (vm : Vm.t) : seq value :=
  [seq vm.[v_var x] | x <- xs].
Definition lget_args (lfd : lfundef) := lget_vars lfd.(lfd_arg).
Definition lget_res  (lfd : lfundef) := lget_vars lfd.(lfd_res).

Definition back_end_pre lfd s t :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: vmt := t.(evm) in
  let: argt := lget_args lfd vmt in
  let: mt := t.(emem) in
  [/\ vmt.[vid tp.(lp_rsp)] = Vword (top_stack ms)
    , vmt.[vid tp.(lp_rip)] = Vword rip
    , values_uincl args argt
    , match_mem ms mt
    , s.(fscs) = t.(escs)
    , vm_initialized_on vmt lfd.(lfd_callee_saved)
    & allocatable_stack ms (lfd_total_stack lfd)
  ].

Definition back_end_post fn lfd s t s' t' :=
  let: ms := s.(fmem) in
  let: mt := t.(emem) in
  let: ress := s'.(fvals) in
  let: ms' := s'.(fmem) in
  let: vmt' := t'.(evm) in
  let: rest := lget_res lfd vmt' in
  let: mt' := t'.(emem) in
  [/\ values_uincl ress rest
    , match_mem ms' mt'
    , s'.(fscs) = t'.(escs)
    & zeroized_s fn ms mt mt'
  ].

Definition lin_sz_pre lp fn lfd i2 i3 :=
  [/\ lin_pre sp lp rip fn i2 i3
    & allocatable_stack i2.(emem) (lfd_total_stack lfd) ].

(* WARNING sz_post uses i3 twice. This might be incorrect, but it makes one of
   the proofs easy. Check if it's true. *)
Definition lin_sz_post szi sp lp fn zfd i1 i3 :=
  rcompose
    (lin_post sp lp fn i1 i3)
    (sz_post szi lp fn zfd i3 i3).

Ltac t_lia := clear; simpl; lia.

Lemma trans_pre_ovm_lin_sz lp fn sfd lfd tfd i1 i3 :
  tp.(lp_rsp) = sp.(p_extra).(sp_rsp) ->
  tp.(lp_rip) = sp.(p_extra).(sp_rip) ->
  tp.(lp_rsp) = lp.(lp_rsp) ->
  tp.(lp_rip) = lp.(lp_rip) ->
  tfd.(lfd_align) = sfd.(f_extra).(sf_align) ->
  tfd.(lfd_align) = lfd.(lfd_align) ->
  tfd.(lfd_export) ->
  tfd.(lfd_export) = lfd.(lfd_export) ->
  tfd.(lfd_callee_saved) = lfd.(lfd_callee_saved) ->
  tfd.(lfd_stk_max) = sfd.(f_extra).(sf_stk_max) ->
  tfd.(lfd_stk_max) = lfd.(lfd_stk_max) ->
  tfd.(lfd_arg) = sfd.(f_params) ->
  get_fundef (p_funcs sp) fn = Some sfd ->
  get_fundef (lp_funcs lp) fn = Some lfd ->
  back_end_pre tfd i1 i3 ->
  exists2 i2, ovm_pre sp rip fn i1 i2 & lin_sz_pre lp fn lfd i2 i3.
Proof.
move=> rsp_tp_sp rip_tp_sp rsp_tp_lp rip_tp_lp al_tfd_sfd al_tfd_lfd exp_tfd
  exp_tfd_lfd cs_tfd_lfd stkmax_tfd_sfd stkmax_tfd_lfd args_tfd_sfd get_sfd
  get_lfd [hrsp hrip] uvals mmem hscs init alloc.
set vs' := lget_args tfd i3.(evm) in uvals.
set i2 := with_vm (estate0 i1) i3.(evm).
exists i2.
- split=> //.
  rewrite get_sfd /=; exists vs'; split; last exact: uvals.
  + by rewrite -rsp_tp_sp hrsp.
  + by rewrite -rip_tp_sp hrip.
  by rewrite get_var_is_allow_undefined -args_tfd_sfd.
rewrite /lin_sz_pre /lin_pre get_sfd get_lfd; split; first split=> //.
- by rewrite -rsp_tp_lp hrsp.
- by rewrite -rip_tp_lp hrip.
- by rewrite -cs_tfd_lfd; apply: init.
- move: alloc; rewrite /allocatable_stack.
  rewrite /lfd_total_stack exp_tfd stkmax_tfd_sfd al_tfd_sfd.
  have /= := wunsigned_range [elaborate stack_limit i2.(emem)].
  t_lia.
rewrite /lfd_total_stack -stkmax_tfd_lfd -al_tfd_lfd -exp_tfd_lfd; exact: alloc.
Qed.

Lemma get_var_is_eq_on wdb s vm vm' xs :
  Sv.Subset (sv_of_list v_var xs) s ->
  vm =[s] vm' ->
  get_var_is wdb vm xs = get_var_is wdb vm' xs.
Proof.
move=> + hvm; elim: xs => [//|x xs ih].
rewrite sv_of_list_cons => hxs.
rewrite /= (get_var_eq_on _ _ hvm); last SvD.fsetdec.
rewrite ih //; SvD.fsetdec.
Qed.

Lemma trans_post_ovm_lin szi lp fn sfd lfd tfd i1 i2 i3 o1 o4 :
  linear_prog (ap_lip aparams) sp = ok lp ->
  get_fundef (p_funcs sp) fn = Some sfd ->
  get_fundef (lp_funcs lp) fn = Some lfd ->
  lfd.(lfd_stk_max) = sfd.(f_extra).(sf_stk_max) ->
  lfd.(lfd_align) = sfd.(f_extra).(sf_align) ->
  tfd.(lfd_align) = lfd.(lfd_align) ->
  tfd.(lfd_res) = lfd.(lfd_res) ->
  lfd.(lfd_export) ->
  tfd.(lfd_stk_max) = lfd.(lfd_stk_max) ->
  ovm_pre sp rip fn i1 i2 ->
  lin_sz_pre lp fn lfd i2 i3 ->
  rcompose (ovm_post sp fn) (lin_sz_post szi sp lp fn tfd i2 i3) o1 o4 ->
  back_end_post fn tfd i1 i3 o1 o4.
Proof.
move=> ok_lp get_sfd get_lfd stkmax_lfd_sfd al_lfd_sfd al_tfd_lfd res_tfd_lfd
  exp_lfd stkmax_tfd_lfd.
move=> + + [o2 + [o3]].
rewrite /ovm_pre /lin_sz_pre /lin_pre /ovm_post /lin_post /sz_post get_sfd
  get_lfd.
move=> [scs_i12 mem_i12 -[vargs [rsp_sp rip_sp hvargs uvargs]]].
(* TODO REMOVE *)
move=> [[rsp_i3 rip_lp init _____alloc vm_i23 scs_i23 mem_i23] alloc].
move=> [scs_o12 mem_o12 [vres [ok_vres uvres]]].
move=> [rsp_o3 mmem_o23 tmu scs_o23 stkstbl].
move=> /(_ _ ok_vres) [vres' ok_vres' uvres'].
rewrite rsp_i3 => -[_ [[<-] scs_o34 vm_o34 mmz_o34]].
split.
- apply/(values_uincl_trans uvres)/(values_uincl_trans uvres').
  move: ok_vres'; rewrite -res_tfd_lfd (get_var_is_eq_on _ _ vm_o34) //.
  rewrite get_var_is_allow_undefined => -[<-].
  exact: values_uincl_refl.
- rewrite mem_o12; move: mmz_o34.
  case: szi => [[szs ows]|] /=; last by move=> <-; apply: mmem_o23.
  move=> mmz_o34.
  set ts_i2 := top_stack i2.(emem).
  set sl_i2 := stack_limit i2.(emem).
  set sm_lfd := lfd.(lfd_stk_max).

  have {}alloc : (* H6 *)
    allocatable_stack
      i2.(emem) (lfd.(lfd_stk_max) + wsize_size lfd.(lfd_align) - 1).
  - by move: alloc; rewrite /allocatable_stack /lfd_total_stack exp_lfd.

  have /= alloc'' : (* H6'' *)
    (lfd.(lfd_stk_max) + wsize_size lfd.(lfd_align) - 1 <= wunsigned ts_i2)%Z.
  + move: alloc; rewrite /allocatable_stack -/ts_i2 -/sl_i2.
    have /= := [elaborate wunsigned_range sl_i2].
    t_lia.

  have /= alloc' : (* H6' *)
    (sfd.(f_extra).(sf_stk_max) + wsize_size sfd.(f_extra).(sf_align) - 1 <=
       wunsigned ts_i2)%Z.
  + by move: alloc''; rewrite stkmax_lfd_sfd al_lfd_sfd.

  have alloc''' : (* H6''' *)
    (0 <= wunsigned (align_word lfd.(lfd_align) ts_i2) - sm_lfd < wbase Uptr)%Z.
  + have: (0 <= sm_lfd)%Z.
    + rewrite /sm_lfd stkmax_lfd_sfd.
      have := [elaborate it_linearization_proof.checked_prog ok_lp get_sfd].
      rewrite /check_fd /=; t_xrbindP=> _ _ _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP
        stk_frame_le_max.
      have := frame_size_bound stk_sz_pos stk_extra_sz_pos.
      move: stk_sz_pos stk_extra_sz_pos stk_frame_le_max.
      t_lia.
    have /= := [elaborate align_word_range lfd.(lfd_align) ts_i2].
    have /= := [elaborate wunsigned_range ts_i2].
    move: alloc alloc''; rewrite /allocatable_stack -/ts_i2 -/sl_i2 -/sm_lfd.
    t_lia.

  set bottom : pointer :=
    (align_word (lfd_align lfd) ts_i2 - wrepr Uptr sm_lfd)%R.
  have bottom_instack :
    zbetween sl_i2 (wunsigned ts_i2 - wunsigned sl_i2) bottom sm_lfd.
  + rewrite /bottom /zbetween !zify.
    move: alloc; rewrite /allocatable_stack.
    have /= := [elaborate align_word_range lfd.(lfd_align) ts_i2].
    rewrite (wunsigned_sub alloc''') -/ts_i2 -/sl_i2 -/sm_lfd; t_lia.

  have no_overflow_bottom: no_overflow bottom sm_lfd.
  + move: bottom_instack; rewrite /no_overflow /zbetween !zify.
    have /= := [elaborate wunsigned_range ts_i2].
    rewrite -/ts_i2 -/sl_i2 -/sm_lfd; t_lia.

  split.
  + move=> /= pr hb hval.
    have := mmem_o23.(read_incl_mem) hb hval.
    rewrite mmz_o34.(read_untouched) // al_tfd_lfd stkmax_tfd_lfd -/bottom.
    apply not_between_U8_disjoint_zrange.
    * exact: no_overflow_bottom.
    move=> /(zbetween_trans bottom_instack).
    rewrite -/(between _ _ _ _) -pointer_range_between => /pointer_rangeP.
    rewrite /sl_i2 /ts_i2 stkstbl.(ss_limit) (ss_top_stack stkstbl).
    have := [elaborate top_stack_below_root _ o2.(emem)].
    rewrite -/(top_stack _) /=; move: o2.(emem) hb.
    t_lia.
  +
    admit.
  + admit.
  admit.
- by rewrite scs_o12 scs_o23 scs_o34.
admit.
Admitted.

Lemma trans_pre_lin_sz_lin_sz lp fn sfd lfd i1 i3 :
  lfd.(lfd_stk_max) = sfd.(f_extra).(sf_stk_max) ->
  lfd.(lfd_align) = sfd.(f_extra).(sf_align) ->
  get_fundef (p_funcs sp) fn = Some sfd ->
  get_fundef (lp_funcs lp) fn = Some lfd ->
  lin_sz_pre lp fn lfd i1 i3 ->
  exists2 i2, lin_pre sp lp rip fn i1 i2 & sz_pre lp lfd i2 i3.
Proof.
move=> stkmax_lfd_sfd al_lfd_sfd get_sfd get_lfd [h alloc].
exists i3; first exact: h.
move: h; rewrite /lin_pre get_sfd get_lfd.
move=> [hrsp hrip init alloc' uvm hscs mmem].
exists (top_stack (emem i1)); split.
- exact: hrsp.
- by [].
- by rewrite stkmax_lfd_sfd al_lfd_sfd; case: alloc'.
move=> p hp.
admit.
Admitted.

Lemma trans_post_lin_sz szi lp fn lfd tfd i1 i2 i4 o1 o3 :
  tfd.(lfd_align) = lfd.(lfd_align) ->
  tfd.(lfd_stk_max) = lfd.(lfd_stk_max) ->
  tfd.(lfd_res) = lfd.(lfd_res) ->
  lin_pre sp lp rip fn i1 i2 ->
  sz_pre lp lfd i2 i4 ->
  rcompose
    (lin_post sp lp fn i1 i2) (sz_post szi lp fn lfd i2 i4) o1 o3 ->
  lin_sz_post szi sp lp fn tfd i1 i4 o1 o3.
Proof.
move=> align_tfd stkmax_tfd res_tfd.
move=> linpre [p [rsp_lp <- hp hvalid]] [o2 linpost szpost]; exists o2 => //.
by rewrite /sz_post align_tfd stkmax_tfd res_tfd; apply: szpost.
Qed.

Lemma it_compiler_back_endP {fn} :
  compiler_back_end aparams cparams entries sp = ok tp ->
  fn \in entries ->
  exists lfd,
    [/\ get_fundef tp.(lp_funcs) fn = Some lfd
      , lfd.(lfd_export)
      & wkequiv_io
          (back_end_pre lfd)
          (isem_stack sp rip fn)
          (isem_linear tp fn)
          (back_end_post fn lfd)
    ].
Proof.
move=> /[dup] /(compiler_back_end_meta print_linearP)
  [rip_tp_sp rsp_tp_sp gd_tp_sp].
rewrite /compiler_back_end; t_xrbindP => ok_export checked_p lp ok_lp.
rewrite print_linearP => zp ok_zp.
rewrite print_linearP => tp' ok_tp.
rewrite print_linearP => ?; subst tp'.
move=> /InP ok_fn.

move: ok_export; rewrite /check_export /= => /allMP - /(_ _ ok_fn).
case get_sfd: get_fundef => [fd|//]; t_xrbindP=> exp_sfd.
set szi := (X in stack_zeroization_lprog _ X) in ok_zp.

set vtmp := var_tmps aparams.
have vtmp_not_magic : disjoint vtmp (magic_variables sp).
- exact: [elaborate var_tmp_not_magic] checked_p.

have get_lfd := [elaborate get_fundef_p' ok_lp get_sfd].
set lfd := (X in _ = Some X) in get_lfd.

have hexp : is_export sp fn by exists fd => //; apply/is_RAnoneP/exp_sfd.

(* Merge varmaps. *)
have wovm := [elaborate
  merge_varmaps_export_call_checkP
    (p := sp) (global_data := rip) (fn := fn) checked_p hexp ] .
set var_tmps := (X in isem_exportcall_check X) in wovm.

(* Linearization *)
have cs_not_arr :
  forall x, Sv.In x one_varmap.callee_saved -> ~ is_aarr (vtype x).
- by move=> x /sv_of_listP /mapP [/= r _ ->]; case: r.
have wlin := [elaborate
  linear_exportcallP
    (hap_hlip haparams) vtmp_not_magic ok_lp cs_not_arr
    (gd := rip) (fn := fn) ].

(* Stack zeroization *)
have [zfd ok_zfd get_zfd] :=
  [elaborate stack_zeroization_lprog_get_fundef ok_zp get_lfd ].
have [rip_lp_zp rsp_lp_zp _] := [elaborate
  stack_zeroization_lprog_invariants ok_zp].
have [_ al_zfd _ arg_zfd _ res_zfd exp_zfd cs_zfd stkmax_zfd _] :=
  [elaborate stack_zeroization_lfd_invariants ok_zfd].

have := istack_zeroization_lprogP_new
  (wE := wE) (rndE0_refl := RndE0Refl) (hap_hszp haparams) _ ok_zp get_lfd.
rewrite ([elaborate lp_rspE ok_lp]) -/szi => /(_ rsp_in_callee_saved) wsz.

(* Tunneling *)
have get_tfd := [elaborate get_fundef_tunnel_program ok_tp get_zfd].
have [rip_zp_tp [rsp_zp_tp [globs_zp_tp _]]] := [elaborate
  tunnel_program_invariants ok_tp].
set tfd := (X in _ = Some X) in get_tfd.

exists tfd; split.
- exact: get_tfd.
- by rewrite /= -exp_zfd /= exp_sfd.

(* Tunneling first because it's equality. *)
apply: wkequiv_io_eutt_r (tunnel_funcs ok_tp fn) _.

(* OVM *)
apply: (wkequiv_io_trans
  (P12 := ovm_pre sp rip fn) (Q12 := fun _ _ => ovm_post sp fn)
  (P23 := lin_sz_pre lp fn lfd) (Q23 := lin_sz_post szi sp lp fn tfd)
  _ _ wovm).
- move=> >.
  apply: (trans_pre_ovm_lin_sz rsp_tp_sp rip_tp_sp) get_sfd get_lfd => //.
  + by rewrite rsp_lp_zp rsp_zp_tp.
  + by rewrite rip_lp_zp rip_zp_tp.
  + by rewrite /tfd -exp_zfd.
- move=> >; apply: (trans_post_ovm_lin ok_lp get_sfd get_lfd).
  + reflexivity.
  + reflexivity.
  + by rewrite -al_zfd.
  + by rewrite -res_zfd.
  + by rewrite /= exp_sfd.
  by rewrite -stkmax_zfd.

(* Linearization *)
apply: (wkequiv_io_trans
  (P12 := lin_pre sp lp rip fn) (Q12 := lin_post sp lp fn)
  (P23 := sz_pre lp lfd) (Q23 := sz_post szi lp fn lfd)
  _ _ wlin).
- by move=> >; apply: trans_pre_lin_sz_lin_sz get_sfd get_lfd.
- move=> >; apply: trans_post_lin_sz.
  + by rewrite al_zfd.
  + by rewrite stkmax_zfd.
  by rewrite res_zfd.

(* Stack zeroization *)
exact: wsz.
Qed.

End BACK_END.

Lemma lget_vars_vmap_of_asm_mem
  (xs : seq var_i) (ys : seq asm_typed_reg) sp_ptr rip_id rsp_id xm :
  mapM typed_reg_of_vari xs = ok ys ->
  lget_vars xs (vmap_of_asm_mem sp_ptr rip_id rsp_id xm)
  = get_typed_reg_values xm ys.
Proof.
elim: xs ys => [|x xs ih] ys /=.
+ by move=> [<-].
t_xrbindP=> r ok_r ys' /ih {}ih ?; subst ys.
rewrite /= -ih; congr cons.
rewrite /typed_reg_of_vari in ok_r.
case: x ok_r => x xi /= ok_r.
by rewrite (asm_typed_reg_of_varI ok_r) get_var_vmap_of_asm_mem.
Qed.

Lemma lget_vars_uincl_asm ripv ls xm xs ys :
  lom_eqv ripv ls xm ->
  mapM typed_reg_of_vari xs = ok ys ->
  values_uincl (lget_vars xs (evm ls)) (get_typed_reg_values xm ys).
Proof.
move=> LM; elim: xs ys => [|x xs ih] ys /=.
+ by move=> [<-]; constructor.
t_xrbindP=> r ok_r ys' /ih {}ih ?; subst ys => /=.
apply: List.Forall2_cons; last exact: ih.
rewrite /typed_reg_of_vari in ok_r.
case: x ok_r => x xi /= ok_r.
rewrite (asm_typed_reg_of_varI ok_r).
case: LM => /= _ _ _ _ R RX X F.
case: r ok_r => r _ /=.
+ exact: R r.
+ exact: RX r.
+ exact: X r.
have Fr := F r.
rewrite /of_rbool; case: (asm_flag xm r) Fr => // b /=;
  by case: ((evm ls).[to_var r]).
Qed.

Lemma vm_init_vmap_of_asm_mem_is_typed_reg sp_ptr rip_id rsp_id xm xs :
  all is_typed_reg xs ->
  vm_initialized_on (vmap_of_asm_mem sp_ptr rip_id rsp_id xm) xs.
Proof.
elim: xs => [|x xs ih] //= /andP [hx /ih{}ih].
apply/andP; split => //.
move: hx; rewrite /is_typed_reg; move=> /andP [hnb /is_okP [r ok_r]].
rewrite /get_var (asm_typed_reg_of_varI ok_r) get_var_vmap_of_asm_mem.
case: r ok_r hnb => /= r ok_r hnb; try by rewrite truncate_word_u.
by move: hnb; rewrite (asm_typed_reg_of_varI ok_r) /=.
Qed.

Lemma vm_init_vmap_of_asm_mem_callee_saved sp_ptr rip_id rsp_id xm rs :
  all (fun r => ~~ is_ABReg r) rs ->
  vm_initialized_on
    (vmap_of_asm_mem sp_ptr rip_id rsp_id xm)
    [seq var_of_asm_typed_reg r | r <- rs].
Proof.
elim: rs => [|r rs ih] //= /andP [hnb /ih{}ih].
apply/andP; split => //.
rewrite /get_var get_var_vmap_of_asm_mem.
move: hnb; case: r => //= ?; by rewrite truncate_word_u.
Qed.

Section BACK_END_TO_ASM.

Context
  (entries : seq funname)
  (sp : sprog (pd := _pd) (asmop := _asmop))
  (xp : asm_prog)
  (rip : pointer)
.

Definition back_end_to_asm_pre xfd s t :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: rm := t.(asm_reg) in
  let: argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let: mt := t.(asm_mem) in
  [/\ rm ad_rsp = top_stack ms
    , t.(asm_rip) = rip
    , values_uincl args argt
    , match_mem ms mt
    , s.(fscs) = t.(asm_scs)
    & allocatable_stack ms xfd.(asm_fd_total_stack)
  ].

Definition back_end_to_asm_post fn xfd s t s' t' :=
  let: ms := s.(fmem) in
  let: mt := t.(asm_mem) in
  let: ress := s'.(fvals) in
  let: ms' := s'.(fmem) in
  let: rest := get_typed_reg_values t' xfd.(asm_fd_res) in
  let: mt' := t'.(asm_mem) in
  [/\ values_uincl ress rest
    , match_mem ms' mt'
    , s'.(fscs) = t'.(asm_scs)
    & zeroized_s fn ms mt mt'
  ].

Lemma it_compiler_back_end_to_asmP {fn} :
  compiler_back_end_to_asm aparams cparams entries sp = ok xp ->
  fn \in entries ->
  exists xfd,
    [/\ get_fundef xp.(asm_funcs) fn = Some xfd
      , xfd.(asm_fd_export)
      & wkequiv_io
          (back_end_to_asm_pre xfd)
          (isem_stack sp rip fn)
          (isem_asm xp fn)
          (back_end_to_asm_post fn xfd)
   ].
Proof.
rewrite /compiler_back_end_to_asm; t_xrbindP=> lp ok_lp ok_xp ok_fn.
have [disj_rip ok_lp_rsp ok_globs ok_funcs] := assemble_progP ok_xp.
have [_ meta_rsp _] := compiler_back_end_meta print_linearP ok_lp.
have rsp_in_callee_saved :
    Sv.In (vid sp.(p_extra).(sp_rsp)) one_varmap.callee_saved.
- rewrite -meta_rsp -ok_lp_rsp.
  apply/sv_of_listP.
  exact: (map_f var_of_asm_typed_reg callee_saved_has_rsp).
have cs_not_arr :
  forall x, Sv.In x one_varmap.callee_saved -> ~ is_aarr (vtype x).
- move=> x /sv_of_listP /mapP [/= r _ ->]; by case: r.

have [lfd [get_lfd lfd_export w_be]] :=
  it_compiler_back_endP (tp := lp) rip rsp_in_callee_saved ok_lp
    ok_fn.
have [xfd ok_get_xfd ok_xfd] := ok_get_fundef ok_xp get_lfd.
case/assemble_fdI: (ok_xfd) =>
  rsp_not_arg ok_callee_saved_lfd
  [] xbody [] xargs [] xres
  [] ok_xbody ok_xargs ok_xres hxfd ok_call_conv.
exists xfd; split => //.
+ by rewrite hxfd /=.
set rip_id := mk_ptr (lp_rip lp).
apply: (
  wkequiv_io_trans
    (P23 := fun (ls : estate) (xm : asmmem) =>
      vm_initialized_on (evm ls)
        [seq var_of_asm_typed_reg i | i <- arch_decl.callee_saved]
      /\ lom_eqv rip_id ls xm)
    (Q23 := fun _ _ ls' xm' => lom_eqv rip_id ls' xm')
    _ _
    w_be
    _
).
- move=> fs xm [hrsp hrip hargs hmm hscs hstk].
  have Meq :=
    lom_eqv_estate_of_asm_mem (top_stack (fmem fs)) (lp_rsp lp) xm disj_rip.
  exists (estate_of_asm_mem (top_stack (fmem fs)) (lp_rip lp) (lp_rsp lp) xm)
    => /=.
  + split => /=.
    * rewrite -hrsp -ok_lp_rsp.
      exact:
        (get_var_vmap_of_asm_mem
           _ (lp_rip lp) (to_ident ad_rsp) xm (ARReg ad_rsp)).
    * rewrite -hrip; by case: Meq.
    * rewrite /lget_args (lget_vars_vmap_of_asm_mem
        (top_stack (fmem fs)) (lp_rip lp) (lp_rsp lp) xm ok_xargs).
      by move: hargs; rewrite hxfd /=.
    * exact: hmm.
    * exact: hscs.
    * exact: (vm_init_vmap_of_asm_mem_is_typed_reg
        (top_stack (fmem fs)) (lp_rip lp) (lp_rsp lp) xm
        ok_callee_saved_lfd).
    * by move: hstk; rewrite hxfd /=.
  split.
  + exact:
      (vm_init_vmap_of_asm_mem_callee_saved
         (top_stack (fmem fs)) (lp_rip lp) (lp_rsp lp) xm
         callee_saved_not_bool).
  exact: Meq.
- move=> fs ls xm fs' xm' _ [_ Meq] [ls' [hvals hmm' hscs' hzero] Meq'].
  split.
  + rewrite hxfd /=.
    apply: (values_uincl_trans hvals).
    exact: (lget_vars_uincl_asm Meq' ok_xres).
  + by case: Meq' => /= _ <- _ _ _ _ _ _; exact: hmm'.
  + case: Meq' => /= heq_scs _ _ _ _ _ _ _.
    by rewrite hscs' heq_scs.
  case: Meq  => /= _ heq_mem  _ _ _ _ _ _.
  case: Meq' => /= _ heq_mem' _ _ _ _ _ _.
  by rewrite -heq_mem -heq_mem'.
move=> ls xm [hvm_init Meq].
exact: (iasm_gen_exportcall (hap_hagp haparams) ok_xp fn hvm_init Meq).
Qed.

End BACK_END_TO_ASM.

Section FULL.

Context
  (entries : seq funname)
  (up : uprog (asmop := _asmop))
  (xp : asm_prog)
.

Definition zeroized_u fn args argt ms mt mt' :=
  cparams.(stack_zero_info) fn <> None ->
  forall p,
    Forall3
      (disjoint_from_writable_param (ep := ep_of_asm_e) p)
      (get_wptrs up fn)
      args argt ->
    zeroized_p ms mt mt' p.

Definition wf_args_x rip fn ms mi args argt :=
  let n := Z.of_nat (size (asm_globs xp)) in
  let ws := get_wptrs up fn in
  let al := get_asm_align_args xp fn in
  wf_args n rip ms mi ws al args argt.

Definition full_pre fn xfd s t :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: rm := t.(asm_reg) in
  let: argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let: mt := t.(asm_mem) in
  exists mi : @mem _pd,
    [/\ mem_agreement_with_ghost ms mt t.(asm_rip) xp.(asm_globs) mi
      , enough_stack_space xp fn (top_stack ms) mt
      , t.(asm_scs) = s.(fscs)
      , rm ad_rsp = top_stack ms
      , wf_args_x t.(asm_rip) fn ms mi args argt
      & Forall3 (value_uincl_or_in_mem mt) (get_wptrs up fn) args argt
    ].

Definition full_post fn xfd s t s' t' :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let: mt := t.(asm_mem) in
  let: ress := s'.(fvals) in
  let: ms' := s'.(fmem) in
  let: rest := get_typed_reg_values t' xfd.(asm_fd_res) in
  let: mt' := t'.(asm_mem) in
  let: n := get_nb_wptr up fn in
  [/\ mem_agreement ms' mt' t'.(asm_rip) xp.(asm_globs)
    , t'.(asm_scs) = s'.(fscs)
    , zeroized_u fn args argt ms mt mt'
    , List.Forall2 (value_in_mem mt') (take n ress) (take n argt)
    & values_uincl (drop n ress) rest
  ].

Lemma it_compile_prog_to_asmP {fn} :
  compile_prog_to_asm aparams cparams entries up = ok xp ->
  fn \in entries ->
  exists xfd,
    [/\ get_fundef xp.(asm_funcs) fn = Some xfd
      , xfd.(asm_fd_export)
      & wkequiv_io
          (full_pre fn xfd)
          (isem_unit up fn)
          (iasmsem_exportcall xp fn)
          (full_post fn xfd)
   ].
Proof.
rewrite /compile_prog_to_asm; t_xrbindP => sp ok_sp ok_xp ok_fn.
have [sfd [xfd [get_sfd get_xfd xfd_export align_args_eq]]] :=
  compiler_back_end_to_asm_get_fundef print_linearP ok_xp ok_fn.
exists xfd; split => //.
move=> fs xm hpre.
case: hpre => mi [hmga hesp hscs_eq hrsp_eq hwfa hfuim].
have FE := it_compiler_front_endP ok_sp ok_fn.

have [xfd2 [get_xfd2 _ BE]] :=
  it_compiler_back_end_to_asmP (asm_rip xm) ok_xp ok_fn.

have heq_xfd : xfd2 = xfd by move: get_xfd2; rewrite get_xfd => [[->]].
subst xfd2.

have [fs_sp [? hsp_scs hsp_eqinmem hsp_uincl hsp_ptr_eq]] :
  exists fs_sp : @fstate extended_op _ ep_of_asm_e sip_of_asm_e,
    [/\ fmem fs_sp = mi
      , fscs fs_sp = fscs fs
      , Forall3 (value_eq_or_in_mem mi) (get_wptrs up fn) (fvals fs) (fvals fs_sp)
      , values_uincl (fvals fs_sp) (get_typed_reg_values xm (asm_fd_arg xfd))
      & Forall3 (fun o v v' => isSome o -> v = v')
                (get_wptrs up fn) (fvals fs_sp)
                (get_typed_reg_values xm (asm_fd_arg xfd))
    ].
- have [hsize1 hsize2] := Forall3_size hfuim.
  have hfuim_mi :
    Forall3 (value_uincl_or_in_mem mi) (get_wptrs up fn) (fvals fs)
      (get_typed_reg_values xm (asm_fd_arg xfd)).
  + apply: (nth_Forall3 None (Vbool true) (Vbool true) hsize1 hsize2) => i hi.
    have := Forall3_nth hfuim None (Vbool true) (Vbool true) hi.
    case ok_writable: (nth None (get_wptrs up fn) i) => [writable|//].
    move=> [pr [ok_pr hread]]; rewrite ok_pr.
    exists pr; split; first by reflexivity.
    move=> off w /[dup] /get_val_byte_bound hoff /hread ok_w.
    move: (hwfa i); rewrite /wf_arg ok_writable ok_pr.
    move=> [_ [[<-] hargp]].
    rewrite -ok_w; apply (match_mem_read_incl_mem hmga.(ma_match_mem)).
    apply hargp.(wap_valid).
    by apply (between_byte hargp.(wap_no_overflow) (zbetween_refl _ _) hoff).
  exists {| fscs := fscs fs; fmem := mi
          ; fvals := map3 (fun o v v' => if o is Some _ then v' else v)
                          (get_wptrs up fn) (fvals fs)
                          (get_typed_reg_values xm (asm_fd_arg xfd)) |}.
  split => /=.
  + reflexivity.
  + reflexivity.
  + elim: hfuim_mi => /=.
    - by constructor.
    - move=> wptr v v' wptrs' vs argt' h _ ih.
      constructor; last exact: ih.
      by case: wptr h.
  + elim: hfuim_mi => /=.
    - by constructor.
    - move=> wptr v v' wptrs' vs argt' h _ ih.
      constructor; last exact: ih.
      case: wptr h => [writable h | h] /=.
      * exact: value_uincl_refl.
      * exact: h.
  + elim: hfuim_mi => /=.
    - by constructor.
    - move=> wptr v v' wptrs' vs argt' _ _ ih.
      constructor; last exact: ih.
      by case: wptr.

subst mi.
have/(FE _ tt) h_fe : front_end_pre up sp (asm_rip xm) fn fn fs fs_sp.
- split.
  - reflexivity.

  - apply: [elaborate enough_stack_space_alloc_ok print_linearP ok_xp ok_fn hmga.(ma_stack_range)].
    by rewrite -(ss_top_stack hmga.(ma_stack_stable)).

  - rewrite /wf_args_s /size_glob.
    rewrite -(compiler_back_end_to_asm_meta print_linearP ok_xp).
    rewrite /get_align_args get_sfd /= align_args_eq.
    move=> i; move: (hwfa i); rewrite /wf_args_x /get_asm_align_args get_xfd /= /wf_arg.
    case hptr: (nth None (get_wptrs up fn) i) => [writable|//].
    move=> [p [hargt_p hargptr]].
    have hi := nth_not_default hptr ltac:(discriminate).
    have hfssp_i : nth (Vbool true) (fvals fs_sp) i =
                   nth (Vbool true) (get_typed_reg_values xm (asm_fd_arg xfd)) i.
    + have := Forall3_nth hsp_ptr_eq None (Vbool true) (Vbool true) hi.
      by rewrite hptr /= => /(_ isT).
    exists p; split; first by rewrite hfssp_i.
    case: hargptr => halign hover hvalid hfresh hwng hdisj.
    split => //.
    move=> hw j vaj pj neq_ij hsome_j hvaj hfssp_j.
    move: hsome_j; case hptr_j: (nth None (get_wptrs up fn) j) => [writablej|//] _.
    have hj := nth_not_default hptr_j ltac:(discriminate).
    have hfssp_j_eq : nth (Vbool true) (fvals fs_sp) j =
                      nth (Vbool true) (get_typed_reg_values xm (asm_fd_arg xfd)) j.
    + have := Forall3_nth hsp_ptr_eq None (Vbool true) (Vbool true) hj.
      by rewrite hptr_j /= => /(_ isT).
    apply: (hdisj hw _ _ _ neq_ij _ hvaj _).
    + by rewrite hptr_j.
    + by rewrite -hfssp_j_eq; exact: hfssp_j.
  - exact: hsp_eqinmem. (* Forall3 (value_eq_or_in_mem (fmem fs_sp)) ... *)
  - have := hmga.(ma_extend_mem).
    by rewrite (compiler_back_end_to_asm_meta print_linearP ok_xp).
  by rewrite hsp_scs. (* fscs fs = fscs fs_sp  <- STEP 1 hsp_scs. *)

have hvalidw_u :=
  [elaborate sem_fun_mem_equiv_uprog
    (wa := withassert)
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (sip := sip_of_asm_e)
    (wsw := nosubword)
    (dc := indirect_c)
    up tt (fn := fn)] dummy_instr_info fs I.
have {}h_fe := lutt_xrutt_trans_l hvalidw_u h_fe.
clear hvalidw_u.

have hvalidw :=
  [elaborate sem_fun_mem_equiv_sprog
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (sip := sip_of_asm_e)
    (wsw := withsubword)
    (dc := direct_c)
    sp (asm_rip xm) (fn := fn)] dummy_instr_info fs_sp I.
have {}h_fe := lutt_xrutt_trans_r hvalidw h_fe.
clear hvalidw.

have /BE h_be : back_end_to_asm_pre (asm_rip xm) xfd fs_sp xm.
- split.
  - by rewrite -(ss_top_stack hmga.(ma_stack_stable)).
  - reflexivity. (* asm_rip xm = asm_rip xm *)
  - exact: hsp_uincl. (* values_uincl (fvals fs_sp) argt — STEP 1 output *)
  - exact: hmga.(ma_match_mem).
  - by rewrite hsp_scs hscs_eq.
  rewrite /allocatable_stack.
  have hrange := hmga.(ma_stack_range).
  have hstk /= := hesp xfd get_xfd.
  rewrite (ss_top_stack hmga.(ma_stack_stable)) in hstk.
  split; first by apply: hstk.1.
  apply: Z.le_trans; first exact: hstk.2.
  apply Z.sub_le_mono_l; exact: hrange.

have hinv := [elaborate
  iasmsem_exportcall_invariantP
    (call_conv := call_conv)
    (asm_scsem := asm_scsem)
    (wE := wE)
    xp fn xm].
have {}h_be := lutt_xrutt_trans_r hinv h_be.
clear hinv.

apply: xrutt_weaken_v1;
  last apply: (xrutt_trans _ h_fe h_be).
- done.
- done.
- move=> T1 T2 [e1|[scs1 n1]] [e2|[scs2 n2]] [T3 [e3|[scs3 n3]]] [_ [_ []]] //.
  + by move=> [_ []].
  + by move=> <- <- [_ []].
  by move=> <- <- [_ [<- <-]].
- move=> T1 T2 e1 t1 e2 t2 hpost T3 e3 [hpre3 hpre13] hpre32.
  case: e1 t1 hpost hpre13 => [[]|e1] t1 // hpost hpre13.
  case: e2 hpost hpre32 => [err2|e2] //= hpost hpre32.
  case: e3 hpre3 hpre13 hpre32 => [err3|e3] //= hpre3 [hpre1 hpre13]
    [_ hpre32] //.
  have [e3' ??] := HandlerContract_trans.(ERpost_trans) hpre13 hpre32 hpost.
  by exists e3'.
- move=> fs' xm' [] fs_sp' h_fe_post h_be_post; split.
  + have [hmem_s [hmem_u [_ _ hext _ _]]] := h_fe_post.
    have [[hrip_eq hss_xm] [_ hmm _ _]] := h_be_post.
    have hglobs := compiler_back_end_to_asm_meta print_linearP ok_xp.
    exists (fmem fs_sp'); split.
    - rewrite -hrip_eq hglobs; exact: hext.
    - exact: hmm.
    - apply: stack_stable_trans; last exact: proj1 hmem_s.
      apply: stack_stable_trans; last exact: hmga.(ma_stack_stable).
      by symmetry; exact: (proj1 hmem_u).
    - rewrite -(ss_limit (proj1 hmem_s)) -(ss_top_stack hss_xm).
      exact: hmga.(ma_stack_range).
  + by have [_ [_ _ <- _]] := h_be_post; have [_ [_ [_ _ _ _ <-]]] := h_fe_post.
  + move=> hszs pr hdisj /negP hnvalid.
    have [[_ hvw] [_ [_ _ _ U _]]] := h_fe_post.
    have [_ [_ m2 _ hzsp]] := h_be_post.
    have [_ mi2 _ _] := hmga.
    have hpr := hzsp hszs pr.
    case: (boolP (validw (fmem fs_sp) Aligned pr U8)) => [hvalid | /hpr //].
    left.
    rewrite
      -(match_mem_read_incl_mem mi2 hvalid) -(match_mem_read_incl_mem m2).
    - rewrite (U _ hvalid hnvalid) //.
      have [hsz1 _] := Forall3_size hsp_ptr_eq.
      have [hsz1' _] := Forall3_size hdisj.
      apply: (nth_Forall3 None (Vbool true) (Vbool true) hsz1' hsz1) => i hi.
      have := Forall3_nth hdisj None (Vbool true) (Vbool true) hi.
      have := Forall3_nth hsp_ptr_eq None (Vbool true) (Vbool true) hi.
      case: (nth None (get_wptrs up fn) i) => [writable|] /=;
        last by move=> _.
      by move=> /(_ isT) ->.
    rewrite -hvw; exact: hvalid.
  + have [_ [_ [hfe1 hfe2 hfe3 hfe4 hfe5]]] := h_fe_post.
    case: h_be_post => [_ [hbe1 hbe2 hbe3 hbe4]].
    have [hsz1 hsz2] := Forall3_size hsp_ptr_eq.
    have heq_take : take (get_nb_wptr up fn) (fvals fs_sp) =
                    take (get_nb_wptr up fn)
                         (get_typed_reg_values xm (asm_fd_arg xfd)).
    { apply: (@eq_from_nth _ (Vbool true)).
      - by rewrite !size_take -hsz1 hsz2.
      - move=> i; rewrite size_take ltn_min => /andP [hlt_n hlt_wptr].
        rewrite -hsz1 in hlt_wptr.
        rewrite nth_take // nth_take //.
        apply: (Forall3_nth hsp_ptr_eq None (Vbool true) (Vbool true)
                            hlt_wptr).
        have hbf := before_find None hlt_n.
        by case: (nth None (get_wptrs up fn) i) hbf. }
    rewrite -heq_take.
    apply: Forall2_impl hfe1 => v1 v2 [pr [-> hread]].
    exists pr; split; first by reflexivity.
    move=> off w /hread; exact: mm_read_ok hbe2.
  move: h_fe_post h_be_post => [_ [_ [_ hfe_uincl _ _ _]]] [_ [hbe_uincl _ _ _]].
  exact: values_uincl_trans hfe_uincl hbe_uincl.
by move=> T1 T2 [?|n1] [?|n2] [_ [_ ?]].
Qed.

End FULL.

End IT.
