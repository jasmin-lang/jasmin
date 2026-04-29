Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

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

Require Import  asm_invariant .

Require Import hoare_valid.
Require Import xrutt xrutt_facts.

Require Import it_compiler_proof.


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

Existing Instance wE.
Existing Instance HandlerContract.
Existing Instance RndE00.
Existing Instance RndE0Refl.
Existing Instance HandlerContract_trans.

Notation it_compiler_front_endP :=
  (it_compiler_front_endP haparams print_uprogP print_sprogP).

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
          (isem_linear tp fn)
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
- (* Transfer hfuim from mt = asm_mem xm to mi *)
  have [hsize1 hsize2] := Forall3_size hfuim.
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
  (* Construct fs_sp with va2 = map3 (ptr → argt, non-ptr → src) *)
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
  + (* hsp_ptr_eq: at pointer positions, fvals fs_sp = argt *)
    elim: hfuim_mi => /=.
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
  (* allocatable_stack (fmem fs_sp) (asm_fd_total_stack xfd)
     mirrors compiler_proof.v:1297-1299 *)
  rewrite /allocatable_stack.
  have hrange := hmga.(ma_stack_range).
  have hstk /= := hesp xfd get_xfd.
  rewrite (ss_top_stack hmga.(ma_stack_stable)) in hstk.
  split; first by apply: hstk.1.
  apply: Z.le_trans; first exact: hstk.2.
  apply Z.sub_le_mono_l; exact: hrange.

have hinv :=
  iasmsem_exportcall_invariantP
    (call_conv := call_conv)
    (asm_scsem := asm_scsem)
    (wE := wE)
    xp fn xm.
have {}h_be := lutt_xrutt_trans_r (hinv _) h_be.
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
