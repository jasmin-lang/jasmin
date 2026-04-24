Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  relational_logic
  sem_one_varmap
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
  merge_varmaps_proof
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

Definition values_uincl := List.Forall2 value_uincl.

Section IT.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {sc_sem : syscall.syscall_sem syscall_state}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
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
  isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (wa := withassert)
    (sip := sip_of_asm_e)
    (scP := sCP_unit)
    (E := E)
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
  isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (wa := noassert)
    (sip := sip_of_asm_e)
    (scP := sCP_stack)
    (E := E)
    (wsw := withsubword)
    (dc := direct_c)
    (pT := progStack)
    sp rip fn fs.

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
  - move => ??? [??] [??] [??] ?? [] -> -> [] -> -> -> /=; eauto.
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
+ by apply: (it_remove_assert_progP (dc:=indirect_c) (sip:=sip_of_asm_e) (pT:=progUnit) (wsw:=nosubword) ev).

apply: (wiequiv_f_trans_EE_EU (wsw2:= withsubword) (dc2:=indirect_c)).
+ exact: it_psem_call_u.

apply: wiequiv_f_trans_UU_EU; first exact (it_wi2w_progP _ _ ok_paw).
apply: wiequiv_f_trans_UU_EU; first exact: (it_insert_renaming_callP (insert_renaming cparams)).
apply: wiequiv_f_trans_UU_EU; first exact: (it_array_copy_fdP _ ok_pa0).
apply: wiequiv_f_trans_EE_EU; first exact: it_add_init_callP.
apply: wiequiv_f_trans_EE_EU; first exact: (it_lower_spill_fdP _ ok_pb).
apply: wiequiv_f_trans_UU_EU.
apply [elaborate it_inliningP (ev := ev) ok_fn ok_pa ].
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
apply: wiequiv_f_trans_EE_EU; first exact:
  (hlop_it_lower_callP
    (hap_hlop haparams)
    (lowering_opt cparams)
    (warning cparams)
    ok_fvars).
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

Let pre : relPreF :=
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

Let post : relPostF :=
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
    rpreF_ := pre;
    rpostF_ := post;
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
    (rpreF23 := pre) (rpostF23 := post)
    _ _
    (it_compiler_first_part ok_p1 ok_fn)
).
- move=> s1 ? [? _]; by exists s1.
- move=> s1 _ s3 r1 r3 [_ <-] [_ halloc hwf hptr hmem hscs] [] r2
    [hscs1 hmem1 hval1] [] hptr' hres hmem' hparams hscs'.
  split=> //; only 3,4: congruence.
  + apply: Forall2_trans hptr'; first exact: value_uincl_value_in_mem_trans.
    exact: (Forall2_take hval1).
  apply: Forall2_trans hres; first exact: value_uincl_trans.
  exact: (Forall2_drop hval1).

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
  (sp : sprog (pd := _pd) (asmop := _asmop))
  (tp : lprog (asmop := _asmop))
  (rip : pointer)
  (rsp_in_callee_saved : Sv.In (vid sp.(p_extra).(sp_rsp)) one_varmap.callee_saved)
.

#[local] Existing Instance withsubword.

Definition lget_vars (xs : seq var_i) (vm : Vm.t) : seq value :=
  [seq vm.[v_var x] | x <- xs].

Definition lget_args lfd := lget_vars lfd.(lfd_arg).
Definition lget_res lfd := lget_vars lfd.(lfd_res).

Definition zeroized_p (ms mt mt' : mem) (p : pointer) : Prop :=
  ~~ validw ms Aligned p U8 ->
  [\/ read mt' Aligned p U8 = read mt Aligned p U8
    | read mt' Aligned p U8 = ok 0%R
  ].

Definition zeroized_s fn ms mt mt' :=
  cparams.(stack_zero_info) fn <> None ->
  forall p, zeroized_p ms mt mt' p.

Let back_end_pre lfd s t :=
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

Let back_end_post fn lfd s t s' t' :=
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

Lemma it_compiler_back_endP {fn} :
  compiler_back_end aparams cparams entries sp = ok tp ->
  fn \in entries ->
  exists lfd,
    [/\ get_fundef tp.(lp_funcs) fn = Some lfd
      , lfd.(lfd_export)
      & wkequiv_io
          (back_end_pre lfd)
          (isem_stack sp rip fn)
          (ilsem_exportcall tp fn)
          (back_end_post fn lfd)
    ].
Proof.
rewrite /compiler_back_end; t_xrbindP => ok_export checked_p lp ok_lp.
rewrite print_linearP => zp ok_zp.
rewrite print_linearP => tp' ok_tp.
rewrite print_linearP => ?; subst tp'.
move=> /InP ok_fn.
set vtmp := var_tmps aparams.
have vtmp_not_magic : disjoint vtmp (magic_variables sp).
- exact: (var_tmp_not_magic (sip := sip_of_asm_e)) checked_p.

(* Linearization provides fd (sprog) and lfd_lp (lp-level). *)
have [fd [lfd_lp [get_sfd get_lfd_lp lp_export w_lin]]] :=
  it_linear_exportcallP (hap_hlip haparams) vtmp_not_magic ok_lp rip (fn := fn).

(* Stack zeroization: zfd has same structural fields as lfd_lp. *)
have [zfd ok_zfd get_zfd] :=
  [elaborate stack_zeroization_lprog_get_fundef ok_zp get_lfd_lp ].
have [inv_info inv_align inv_tyin inv_arg inv_tyout inv_res inv_export
     inv_cs inv_stkmax [inv_framesize inv_align_args]] :=
  [elaborate stack_zeroization_lfd_invariants ok_zfd ].

(* Tunneling: tunnel_lfundef fn zfd is the final lfd. *)
have! get_tfd := (get_fundef_tunnel_program ok_tp get_zfd).
have! [rip_eq [rsp_eq [globs_eq _]]] := (tunnel_program_invariants ok_tp).
have! [rip_eq' rsp_eq' _] := (stack_zeroization_lprog_invariants ok_zp).

(* Conclude the existential. *)
exists (tunneling.tunnel_lfundef fn zfd).
split.
- exact: get_tfd.
- by rewrite /= -inv_export.

(* Reduce via tunneling: replace [ilsem_exportcall tp fn] by its
   eutt-equivalent [ilsem_exportcall zp fn]. *)
apply: wkequiv_io_eutt_r (tunnel_funcs ok_tp fn) _.

apply: (wkequiv_io_trans _ _ w_lin); cycle 2.
- apply: (istack_zeroization_lprogP_new (hap_hszp haparams) _ ok_zp get_lfd_lp).
  + have hrsp_eq : lp_rsp lp = sp_rsp sp.(p_extra)
      by move: ok_lp; rewrite /linear_prog; t_xrbindP => _ _ _ <-.
    by rewrite hrsp_eq.
- (* pre decomposition *)
  move=> fs s [] hrsp hrip hargs hm hscs hinit halloc.
  have halloc_lin :
    allocatable_stack (fmem fs)
      (sf_stk_max (f_extra fd) + wsize_size (sf_align (f_extra fd)) - 1).
  - move: halloc; rewrite /allocatable_stack /lfd_total_stack /tunneling.tunnel_lfundef /=.
    rewrite -inv_export -inv_stkmax -inv_align lp_export /=.
    have! hlfd_stk := (get_fundef_p' ok_lp get_sfd).
    rewrite get_lfd_lp in hlfd_stk.
    injection hlfd_stk => {}hlfd_stk.
    rewrite hlfd_stk /=.
    by [].
  have hle_top :
    (sf_stk_max (f_extra fd) + wsize_size (sf_align (f_extra fd)) - 1
      <= wunsigned (top_stack (fmem fs)))%Z.
  - move: halloc_lin; rewrite /allocatable_stack.
    have /= := [elaborate (wunsigned_range (stack_limit (fmem fs)))].
    lia.
  exists s.
  + split.
    - by rewrite rsp_eq' rsp_eq hrsp.
    - exact: hm.
    - by rewrite /linearization_proof.lget_args inv_arg.
    - by rewrite rip_eq' rip_eq hrip.
    - by rewrite inv_cs.
    - exact: hscs.
    - exact: hle_top.
    exact: halloc_lin.
  exists (top_stack (fmem fs)).
  have align_range : (wunsigned (top_stack (fmem fs)) - wsize_size (lfd_align lfd_lp) <
   wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem fs))) <=
   wunsigned (top_stack (fmem fs)))%Z.
  - have /= := [elaborate (align_word_range (lfd_align lfd_lp) (top_stack (fmem fs)))]. by [].
  have top_range : (0 <= wunsigned (top_stack (fmem fs)) < wbase Uptr)%Z.
  - have /= := [elaborate (wunsigned_range (top_stack (fmem fs)))]. by [].
  have stk_range : (0 <= wunsigned (stack_limit (fmem fs)) < wbase Uptr)%Z.
  - have /= := [elaborate (wunsigned_range (stack_limit (fmem fs)))]. by [].
  have halloc' :
    (0 <= lfd_stk_max lfd_lp + wsize_size (lfd_align lfd_lp) - 1 <=
     wunsigned (top_stack (fmem fs)) - wunsigned (stack_limit (fmem fs)))%Z.
  - move: halloc; rewrite /allocatable_stack /lfd_total_stack /tunneling.tunnel_lfundef /=.
    by rewrite -inv_export -inv_stkmax -inv_align lp_export /=.
  have! hlfd_stk := (get_fundef_p' ok_lp get_sfd).
  rewrite get_lfd_lp in hlfd_stk.
  injection hlfd_stk => {}hlfd_stk.
  have stk_max_eq : lfd_stk_max lfd_lp = sf_stk_max (f_extra fd).
  - by rewrite hlfd_stk.
  have! := (linearization_proof.checked_prog ok_lp get_sfd).
  rewrite /check_fd /=; t_xrbindP=> _ _ _ _ ok_stk_sz _ _ _.
  case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
  have hfb := frame_size_bound stk_sz_pos stk_extra_sz_pos.
  have lfd_stk_pos : (0 <= lfd_stk_max lfd_lp)%Z.
  - rewrite stk_max_eq.
    eapply Z.le_trans; last exact stk_frame_le_max.
    eapply Z.le_trans; last exact hfb. lia.
  have H6''' :
    (0 <= wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem fs))) - lfd_stk_max lfd_lp < wbase Uptr)%Z.
  - split.
    + lia.
    + have upper : (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem fs))) < wbase Uptr)%Z.
      * eapply Z.le_lt_trans; last exact (proj2 top_range).
        apply align_range.
      lia.
  have bottom_instack:
    zbetween
      (stack_limit (fmem fs))
      (wunsigned (top_stack (fmem fs)) - wunsigned (stack_limit (fmem fs)))
      (align_word (lfd_align lfd_lp) (top_stack (fmem fs))
       - wrepr Uptr (lfd_stk_max lfd_lp))%R
      (lfd_stk_max lfd_lp).
  - rewrite /zbetween !zify.
    rewrite wunsigned_sub //. lia.
  split=> //.
  + by rewrite rsp_eq' rsp_eq hrsp.
  + move: halloc.
    rewrite /allocatable_stack /lfd_total_stack /tunneling.tunnel_lfundef /=.
    rewrite -inv_export -inv_stkmax -inv_align lp_export /=.
    have /= := [elaborate (wunsigned_range (stack_limit (fmem fs)))].
    lia.
  rewrite /valid_between.
  move=> pr /(zbetween_trans bottom_instack).
  rewrite -/(between _ _ _ _) -pointer_range_between => hpr.
  apply hm.(valid_stk).
  apply /pointer_rangeP.
  apply: pointer_range_incl_r hpr.
  exact: top_stack_below_root.

(* post composition: combine linearization post with stack-zero post *)
(* Target post: values_uincl, match_mem, fscs_eq, zeroized_s *)
move=> i1 i2 i3 o1 o3
  [hrsp hmem hargs hrip hinit hscs hbound]
  halloc
  [ptr [hrsp_eq heq hle hvalid_btw]]
  [o2
     [hrsp_o2 hmem_o2 tmu hvals_o2 hscs_o2 hss halloc_lin]
     [ptr' [hrsp_eq' hscs_eq hvm_eq hmmz]]
  ].
subst i3.
move: hrsp_eq hrsp_eq'; rewrite hrsp => -[] ?; subst ptr => -[] ?; subst ptr'.
set bottom : pointer := (align_word (lfd_align lfd_lp) (top_stack (fmem i1))
               - wrepr Uptr (lfd_stk_max lfd_lp))%R.
have! hlfd_stk := (get_fundef_p' ok_lp get_sfd).
rewrite get_lfd_lp in hlfd_stk.
injection hlfd_stk => {}hlfd_stk.
have stk_max_eq : lfd_stk_max lfd_lp = sf_stk_max (f_extra fd)
  by rewrite hlfd_stk.
have align_eq : lfd_align lfd_lp = sf_align (f_extra fd)
  by rewrite hlfd_stk.
have! := (linearization_proof.checked_prog ok_lp get_sfd).
rewrite /check_fd /=; t_xrbindP=> _ _ _ _ ok_stk_sz _ _ _.
case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
have hfb := frame_size_bound stk_sz_pos stk_extra_sz_pos.
have lfd_stk_pos : (0 <= lfd_stk_max lfd_lp)%Z.
- rewrite stk_max_eq.
  eapply Z.le_trans; last exact stk_frame_le_max.
  eapply Z.le_trans; last exact hfb. lia.
have top_range : (0 <= wunsigned (top_stack (fmem i1)) < wbase Uptr)%Z
  by have /= := [elaborate (wunsigned_range (top_stack (fmem i1)))].
have stk_range : (0 <= wunsigned (stack_limit (fmem i1)) < wbase Uptr)%Z
  by have /= := [elaborate (wunsigned_range (stack_limit (fmem i1)))].
have align_range : (wunsigned (top_stack (fmem i1)) - wsize_size (lfd_align lfd_lp) <
 wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) <=
 wunsigned (top_stack (fmem i1)))%Z
  by have /= := [elaborate (align_word_range (lfd_align lfd_lp) (top_stack (fmem i1)))].
have halloc_lp :
  (0 <= lfd_stk_max lfd_lp + wsize_size (lfd_align lfd_lp) - 1 <=
   wunsigned (top_stack (fmem i1)) - wunsigned (stack_limit (fmem i1)))%Z.
- have := wsize_size_pos (lfd_align lfd_lp).
  have heq1 := stk_max_eq.
  have heq2 := align_eq.
  move: halloc_lin.
  by rewrite /allocatable_stack heq1 heq2.
have H6''' :
  (0 <= wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) - lfd_stk_max lfd_lp < wbase Uptr)%Z.
- split; first lia.
  have upper : (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) < wbase Uptr)%Z.
  + by eapply Z.le_lt_trans; [apply align_range | apply (proj2 top_range)].
  lia.
have bottom_instack:
  zbetween
    (stack_limit (fmem i1))
    (wunsigned (top_stack (fmem i1)) - wunsigned (stack_limit (fmem i1)))
    bottom
    (lfd_stk_max lfd_lp).
- rewrite /bottom /zbetween !zify.
  rewrite wunsigned_sub //. lia.
have no_overflow_bottom : no_overflow bottom (lfd_stk_max lfd_lp).
- move: bottom_instack; rewrite /no_overflow /zbetween !zify.
  lia.
split.
- (* values_uincl *)
  rewrite /lget_res /lget_vars /= -inv_res.
  suff heq : [seq (evm o3).[v_var x] | x <- lfd_res lfd_lp]
           = [seq (evm o2).[v_var x] | x <- lfd_res lfd_lp].
  + by rewrite heq; exact: hvals_o2.
  apply map_ext => x hin.
  symmetry; apply: hvm_eq.
  by apply /sv_of_listP /in_map; exists x.
- (* match_mem: combine hmem_o2 (match_mem fmem_o1 / emem_o2) with
     hmmz (match_mem_zero_export emem_o2 / emem_o3) *)
  move: hmmz; rewrite /match_mem_zero_export -/bottom /=.
  case: (cparams.(stack_zero_info) fn) => [[szs ows]|] /=; last first.
  + by move=> <-.
  move=> hmm; split.
  + move=> pr hb hval.
    have := hmem_o2.(read_incl_mem) hb hval.
    rewrite hmm.(read_untouched) //.
    apply: not_between_U8_disjoint_zrange => //.
    move=> /(zbetween_trans bottom_instack).
    rewrite -/(between _ _ _ _) -pointer_range_between => /pointer_rangeP hpr.
    apply: hb.
    by rewrite -(ss_limit hss) -(ss_top_stack hss).
  + move=> pr w hb ok_w.
    (* hb says pr is in stack region of (fmem o1), but such pr is not valid,
       contradicting readV ok_w *)
    exfalso; apply/negP/(stack_region_is_free (m := fmem o1) (p := pr)).
    * by rewrite (readV ok_w).
    move: hb; rewrite /pointer_range.
    by rewrite -/(top_stack _); lia.
  + by move=> pr /hmem_o2.(valid_incl); rewrite hmm.(valid_eq).
  move=> pr.
  rewrite -hmm.(valid_eq).
  by apply hmem_o2.(valid_stk).
- by rewrite hscs_o2 hscs_eq.

(* zeroized_s *)
move=> hi; move: hmmz; rewrite /match_mem_zero_export.
case hszs: stack_zero_info => [[szs ows]|] //= hmm pr hnvalid.
case hb: (between bottom (lfd_stk_max lfd_lp) pr U8).
+ by right; rewrite (hmm.(read_zero) hb).
left; rewrite -hmm.(read_untouched); last first.
+ apply not_between_U8_disjoint_zrange => //.
  by apply /negP /negPf.
rewrite -tmu //.
- by apply/negP.
(* ~ pointer_range (sp0 - wrepr max0) sp0 pr *)
move: ok_zfd; rewrite /stack_zeroization_lfd hszs.
have lp_export' : lfd_export lfd_lp && (0 <? lfd_stk_max lfd_lp)%Z =
                  (0 <? lfd_stk_max lfd_lp)%Z
  by rewrite lp_export.
rewrite lp_export' /=.
case: ZltP => [Hmaxpos | Hmaxnpos]; last first.
{ (* lfd_stk_max = 0: range is empty *)
  move=> _.
  have Hmax0 : sf_stk_max (f_extra fd) = 0%Z.
  { rewrite -stk_max_eq. apply: Z.le_antisymm lfd_stk_pos.
    by apply/Z.nlt_ge/Hmaxnpos. }
  rewrite Hmax0 wrepr0 GRing.subr0.
  rewrite /pointer_range; move=> /andP [/ZleP Ha /ZltP Hb]; lia. }
rewrite /stack_zeroization_lfd_body; t_xrbindP => halign _ _ _ _ _.
have hexp : is_RAnone (sf_return_address (f_extra fd)) by move: lp_export; rewrite hlfd_stk /=.
have Hframe_eq : lfd_frame_size lfd_lp = (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z.
  by rewrite hlfd_stk /= /frame_size hexp.
have Hsum_nn : (0 <= sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z
  := Z.add_nonneg_nonneg _ _ stk_sz_pos stk_extra_sz_pos.
have Hws : (0 < wsize_size (sf_align (f_extra fd)))%Z := wsize_size_pos _.
have Hmax_le_top : (sf_stk_max (f_extra fd) <= wunsigned (top_stack (fmem i1)))%Z.
  apply: (Z.le_trans _ (lfd_stk_max lfd_lp + wsize_size (lfd_align lfd_lp) - 1)%Z _ _ hle).
  rewrite stk_max_eq.
  generalize (wsize_size_pos (lfd_align lfd_lp)). clear. intros. lia.
have Hsum_le_top : (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) <=
                    wunsigned (top_stack (fmem i1)))%Z.
  apply: (Z.le_trans _ _ _ hfb).
  apply: (Z.le_trans _ _ _ stk_frame_le_max Hmax_le_top).
have Hrng : (0 <= wunsigned (top_stack (fmem i1)) -
             (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)) < wbase Uptr)%Z.
  split.
  - generalize Hsum_le_top. clear. intros. lia.
  - generalize top_range Hsum_nn. clear. intros. lia.
have Halign_final :
  is_align (Pointer := WArray.PointerZ)
    (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z (sf_align (f_extra fd)).
  by move: halign; rewrite Hframe_eq align_eq.
rewrite /align_top_stack ([elaborate align_top_aligned Hsum_nn Hrng Halign_final]).
rewrite pointer_range_between.
rewrite -align_eq.
have Hbottom_eq :
  (align_word (lfd_align lfd_lp) (top_stack (fmem i1)) -
   wrepr Uptr (sf_stk_max (f_extra fd)))%R = bottom.
  by rewrite /bottom stk_max_eq.
rewrite Hbottom_eq.
have Hsize_eq :
  (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) -
   wunsigned bottom)%Z = lfd_stk_max lfd_lp.
  rewrite /bottom wunsigned_sub; last first.
  - split; first exact: (proj1 H6''').
    apply: (Z.le_lt_trans _ (wunsigned (top_stack (fmem i1)))); last exact (proj2 top_range).
    apply: (Z.le_trans _ (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))))).
    + generalize lfd_stk_pos. clear. intros. lia.
    + apply (proj2 align_range).
  generalize (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1)))) (lfd_stk_max lfd_lp).
  clear. intros. lia.
rewrite Hsize_eq.
by apply/negP; rewrite hb.
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
          (iasmsem_exportcall xp fn)
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
have [lfd [get_lfd lfd_export w_be]] :=
  it_compiler_back_endP (tp := lp) rip rsp_in_callee_saved ok_lp ok_fn.
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
- (* hpre: build intermediate estate from asmmem *)
  move=> fs xm [hrsp hrip hargs hmm hscs hstk].
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
- (* hpost: combine the back-end post and the lom_eqv bridge *)
  move=> fs ls xm fs' xm' _ [_ Meq] [ls' [hvals hmm' hscs' hzero] Meq'].
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
(* bridge step: iasm_gen_exportcall *)
move=> ls xm [hvm_init Meq].
exact: (iasm_gen_exportcall (hap_hagp haparams) ok_xp fn hvm_init Meq).
Qed.

End BACK_END_TO_ASM.

End IT.
