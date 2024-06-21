From mathcomp Require Import all_ssreflect all_algebra.

Require Import
  arch_params_proof
  compiler
  compiler_util
  psem
  psem_facts.
Require Import
  allocation_proof
  lower_spill_proof
  inline_proof
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
  remove_globals_proof
  remove_assert_proof
  stack_alloc_proof_2
  tunneling_proof
  linearization_proof
  merge_varmaps_proof
  psem_of_sem_proof
  slh_lowering_proof
  direct_call_proof
  stack_zeroization_proof.

Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen_proof
  sem_params_of_arch_extra.
Import Utf8.
Import wsize.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance withsubword.

Section PROOF.

Context
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra} {call_conv : calling_convention} {asm_scsem : asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options).

Hypothesis print_uprogP : forall s p, cparams.(print_uprog) s p = p.
Hypothesis print_sprogP : forall s p, cparams.(print_sprog) s p = p.
Hypothesis print_linearP : forall s p, cparams.(print_linear) s p = p.

#[local]
Existing Instance progUnit.

Lemma postprocessP {dc : DirectCall} (p p': uprog) ev scs m fn va scs' m' vr va' :
  dead_code_prog (ap_is_move_op aparams) (const_prop_prog p) false = ok p' →
  sem_call p ev scs m fn va scs' m' vr →
  List.Forall2 value_uincl va va' →
  exists2 vr',
    sem_call p' ev scs m fn va' scs' m' vr'
    & List.Forall2 value_uincl vr vr'.
Proof.
  move => ok_p' E A.
  have [ vr1 [ {} E R1 ] ] := const_prop_callP E A.
  have! [ vr2 [ E' R2 ] ] :=
    (dead_code_callPu
      (hap_is_move_opP haparams)
      ok_p'
      (List_Forall2_refl _ value_uincl_refl)
      E).
  exists vr2; first exact: E'.
  apply: Forall2_trans R1 R2.
  exact: value_uincl_trans.
Qed.

Lemma unrollP  {dc : DirectCall} (fn : funname) (p p' : prog) ev scs mem va va' scs' mem' vr :
  unroll_loop (ap_is_move_op aparams) p = ok p'
  -> sem_call p ev scs mem fn va scs' mem' vr
  -> List.Forall2 value_uincl va va'
  -> exists vr',
       sem_call p' ev scs mem fn va' scs' mem' vr'
       /\ List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll_loop; t_xrbindP.
  elim: Loop.nb p va va' vr => //= n Hn p va va' vr p1 ok_p1.
  case e: unroll_prog => [ p2 [] ]; last first.
  { move/ok_inj => {n Hn} <- E A.
    have [ vr' {} E R ] := postprocessP ok_p1 E A.
    by exists vr'. }
  t_xrbindP => p3 ok_p3 ok_p' E A.
  have [ vr1 {} E R1 ] := postprocessP ok_p1 E (List_Forall2_refl _ value_uincl_refl).
  have := unroll_callP E.
  rewrite e /= => {} E.
  have [ vr2 [] {} E R2 ] := Hn _ _ _ _ _ ok_p3 ok_p' E A.
  exists vr2; split; first exact: E.
  apply: Forall2_trans R1 R2.
  exact: value_uincl_trans.
Qed.

Definition compose_pass : ∀ vr (P Q: _ → Prop),
        (∀ vr', P vr' → Q vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
    := λ vr P Q h x, let 'ex_intro2 vr' u p := x in ex_intro2 _ _ vr' u (h vr' p).

Definition compose_pass_uincl : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → ∃ vr', Q vr' ∧ List.Forall2 value_uincl vr vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro2 vr1 u p := x in
      let 'ex_intro vr2 (conj q v) := h _ p in
      ex_intro2 _ _ vr2 (Forall2_trans value_uincl_trans u v) q.

Definition compose_pass_uincl' : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → exists2 vr', List.Forall2 value_uincl vr vr' & Q vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro2 vr1 u p := x in
      let 'ex_intro2 vr2 v q := h _ p in
      ex_intro2 _ _ vr2 (Forall2_trans value_uincl_trans u v) q.

Lemma live_range_splittingP {dc : DirectCall} (p p': uprog) scs m fn va scs' m' vr :
  live_range_splitting aparams cparams p = ok p' →
  sem_call p tt scs m fn va scs' m' vr →
  exists2 vr',
      List.Forall2 value_uincl vr vr' &
      sem_call p' tt scs m fn va scs' m' vr'.
Proof.
  rewrite /live_range_splitting; t_xrbindP.
  rewrite !print_uprogP => ok_p' pa ok_pa.
  rewrite print_uprogP => ? exec_p; subst pa.
  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: compose_pass_uincl.
  - move=> vr' Hvr'.
    apply: (dead_code_callPu (hap_is_move_opP haparams) ok_pa va_refl).
    exact: Hvr'.
  apply: compose_pass_uincl;
    first by move => vr';
             apply: (alloc_call_uprogP (sip := sip_of_asm_e) ok_p').
  exists vr.
  - exact: (List_Forall2_refl _ value_uincl_refl).
  by rewrite surj_prog.
Qed.

Lemma values_uincl_refl vs :
  List.Forall2 value_uincl vs vs.
Proof. exact: List_Forall2_refl value_uincl_refl. Qed.

Lemma inliningP (to_keep: seq funname) (p p': uprog) scs m fn va scs' m' vr :
  inlining cparams to_keep p = ok p' →
  fn \in to_keep →
  sem_call (wsw := withsubword) (dc := indirect_c) p tt scs m fn va scs' m' vr →
  exists2 vr', List.Forall2 value_uincl vr vr' & sem_call (dc := indirect_c) p' tt scs m fn va scs' m' vr'.
Proof.
  rewrite /inlining /=; t_xrbindP => pa.
  rewrite print_uprogP => ok_pa pb ok_pb.
  rewrite print_uprogP => <- {p'} ok_fn h.
  apply: compose_pass.
  - by move => vr'; exact: (dead_calls_err_seqP (sip := sip_of_asm_e) (sCP := sCP_unit) ok_pb).
  exact: (inline_call_errP ok_pa (values_uincl_refl va) h).
Qed.

Lemma compiler_first_partP entries (p: prog) (p': uprog) scs m fn va scs' m' vr :
  compiler_first_part aparams cparams entries p = ok p' →
  fn \in entries →
  sem_call (wsw:= nosubword) (dc:=indirect_c) p tt scs m fn va scs' m' vr →
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    sem_call (dc:=direct_c) p' tt scs m fn va scs' m' vr'.
Proof.
  rewrite /compiler_first_part; t_xrbindP => pa0.
  rewrite print_uprogP => ok_pa0 pb.
  rewrite print_uprogP => ok_pb pa.
  rewrite print_uprogP => ok_pa pc ok_pc.
  rewrite !print_uprogP => pd ok_pd.
  rewrite !print_uprogP => pe ok_pe.
  rewrite !print_uprogP => pf ok_pf.
  rewrite !print_uprogP => pg ok_pg.
  rewrite !print_uprogP => ph ok_ph pi ok_pi.
  rewrite !print_uprogP => ok_fvars pj ok_pj pp.
  rewrite !print_uprogP => ok_pp <- {p'} ok_fn exec_p.

  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: compose_pass_uincl.
  - move=> vr'; apply: (pi_callP (sCP := sCP_unit) ok_pp va_refl).
   apply: compose_pass.
  - move=> vr'.
    assert (h := lower_slh_prog_sem_call (dc:=direct_c) (hap_hshp haparams) (ev:= tt) ok_pj).
    apply h => //.
  apply: compose_pass.
  - move => vr'.
    exact:
      (hlop_lower_callP
         (hap_hlop haparams)
         (lowering_opt cparams)
         (warning cparams)
         ok_fvars).
  apply: compose_pass; first by move => vr'; apply: (RGP.remove_globP ok_pi).
  apply: compose_pass_uincl'.
  - move => vr'; apply: (live_range_splittingP ok_ph).
  apply: compose_pass.
  - move=> vr' hvr'. assert (h := expand_callP (sip := sip_of_asm_e) ok_pg); apply h => //; apply hvr'.
  apply: compose_pass_uincl'.
  - by move=>  vr'; apply: indirect_to_direct.
  apply: compose_pass.
  - by move=> vr'; apply: (makeReferenceArguments_callP (siparams := sip_of_asm_e) ok_pf).
  apply: compose_pass_uincl; first by move =>vr'; apply: (remove_init_fdPu _ va_refl).
  apply: compose_pass_uincl'.
  - move => vr' Hvr'.
    apply: (live_range_splittingP ok_pe); exact: Hvr'.
  apply: compose_pass.
  - by move => vr'; exact: (dead_calls_err_seqP (sip := sip_of_asm_e) (sCP := sCP_unit) ok_pd).
  apply: compose_pass_uincl; first by move=> vr' Hvr'; apply: (unrollP ok_pc _ va_refl); exact: Hvr'.
  apply: compose_pass_uincl'; first by move => vr' Hvr'; apply: (inliningP ok_pa ok_fn); exact: Hvr'.
  apply: compose_pass.
  - by move=> vr'; apply: (lower_spill_fdP (sip := sip_of_asm_e) (sCP := sCP_unit) ok_pb).
  apply: compose_pass; first by move => vr'; apply: (add_init_fdP).
  apply: compose_pass_uincl.
  - by move=> vr'; apply:(array_copy_fdP (sCP := sCP_unit) ok_pa0 va_refl).
  apply: compose_pass;first by move => vr' ; apply: (remove_assert_fdP).
  apply: compose_pass; first by move => vr'; exact: psem_call_u.
  exists vr => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
Qed.

Lemma check_removereturnP entries remove_return b :
  check_removereturn entries remove_return = ok b →
  ∀ fn, fn \in entries → remove_return fn = None.
Proof.
  move => /assertP /eqP h fn /(in_pmap remove_return).
  case: (remove_return fn) => // r.
  by rewrite h.
Qed.

Lemma compiler_third_partP entries (p p' : @sprog _pd _ _asmop) :
  compiler_third_part aparams cparams entries p = ok p' →
  [/\
    ∀ fn (gd: pointer) scs m va scs' m' vr,
      fn \in entries →
      sem_call (dc:= direct_c) p gd scs m fn va scs' m' vr →
      exists2 vr',
      List.Forall2 value_uincl vr vr' &
      sem_call (dc:= direct_c) p' gd scs m fn va scs' m' vr' &
    ∀ fn m,
      alloc_ok p' fn m → alloc_ok p fn m
  ].
Proof.
  rewrite /compiler_third_part; t_xrbindP=> /check_removereturnP ok_rr pa ok_pa.
  rewrite !print_sprogP => ok_pb pc ok_pc.
  rewrite print_sprogP => <- {p'}.
  split.
  + move => fn gd scs m va scs' m' vr ok_fn exec_p.
    have va_refl : List.Forall2 value_uincl va va.
    - exact: List_Forall2_refl.
    apply: compose_pass_uincl.
    - move => vr'.
      apply: (dead_code_callPs (dc:= direct_c) (hap_is_move_opP haparams) ok_pc va_refl).
    apply: compose_pass_uincl;
      first by move => vr';
        apply:
          (alloc_call_sprogP (ep := ep_of_asm_e) (sip := sip_of_asm_e) ok_pb).
    rewrite surj_prog.
    have! [vr' [exec_pa]] :=
      (dead_code_tokeep_callPs (hap_is_move_opP haparams) ok_pa va_refl exec_p).
    rewrite /fn_keep_only (ok_rr _ ok_fn) => vr_vr'.
    by exists vr'.
  rewrite /alloc_ok => fn m alloc_pc fd get_fd.
  have! [fda ok_fda get_fda] :=
    (dead_code_prog_tokeep_get_fundef ok_pa get_fd).
  have [fdb [get_fdb ok_fdb]] :=
    allocation_proof.all_checked (sip := sip_of_asm_e) ok_pb get_fda.
  have! [fdc ok_fdc get_fdc] :=
    (dead_code_prog_tokeep_get_fundef ok_pc get_fdb).
  move: (alloc_pc _ get_fdc).
  have [_ _ ->]:= dead_code_fd_meta ok_fdc.
  rewrite /sf_total_stack.
  have [ <- <- <- ] := @check_fundef_meta _ _ _ _ _ _ _ (_, fda) _ _ _ ok_fdb.
  have [_ _ ->]:= dead_code_fd_meta ok_fda.
  done.
Qed.

Lemma compiler_third_part_meta entries (p p' : sprog) :
  compiler_third_part aparams cparams entries p = ok p' →
  p_extra p' = p_extra p.
Proof.
  rewrite /compiler_third_part.
  t_xrbindP => _ pa hpa _ pb hpb.
  have! [_ ok_pa] := (dead_code_prog_tokeep_meta hpa).
  have! [] := (dead_code_prog_tokeep_meta hpb).
  rewrite !print_sprogP /= => _ ok_pb <- {p'}.
  by rewrite ok_pb ok_pa.
Qed.

(* TODO: move *)
Remark sp_globs_stack_alloc rip rsp data ga la (p: uprog) (p': sprog) :
  alloc_prog (ap_shp aparams) (ap_sap aparams) (fresh_var_ident cparams (Reg (Normal, Direct)) dummy_instr_info) rip rsp data ga la p = ok p' →
  sp_globs (p_extra p') = data.
Proof.
  by rewrite /alloc_prog; t_xrbindP => ???? _ <-.
Qed.

Lemma compiler_third_part_alloc_ok entries (p p' : sprog) (fn: funname) (m: mem) :
  compiler_third_part aparams cparams entries p = ok p' →
  alloc_ok p' fn m →
  alloc_ok p fn m.
Proof. case/compiler_third_partP => _; exact. Qed.

Lemma check_no_ptrP entries ao u fn :
  check_no_ptr entries ao = ok u →
  fn \in entries →
  allNone (sao_params (ao fn)) ∧ allNone (sao_return (ao fn)).
Proof.
  clear.
  case: u => /allMP h /InP ok_fn; move: (h _ ok_fn).
  by t_xrbindP.
Qed.

Lemma allNone_nth {A} (m: seq (option A)) i :
  allNone m ->
  nth None m i = None.
Proof.
  elim: m i.
  - by move => ? _; exact: nth_nil.
  by case => // m ih [].
Qed.

Lemma sem_call_length {dc:DirectCall}(p: uprog) scs m fn va scs' m' vr :
  sem_call p tt scs m fn va scs' m' vr →
  ∃ fd,
    [/\ get_fundef (p_funcs p) fn = Some fd,
     size (f_params fd) = size va,
     size (f_tyin fd) = size va,
     size (f_tyout fd) = size vr &
     size (f_res fd) = size vr].
Proof.
  move=> h; have := sem_callE h => -[] fd [] -> [] va' [] ? [] ? [] ? [] vr' [] ok_args [] _ ok_va' _ [] /size_mapM ok_vr' ok_res _.
  have := size_fold2 ok_va'.
  have [<- <-] := size_mapM2 ok_args.
  have [size_vr' <-] := size_mapM2 ok_res.
  rewrite {2}size_vr' -ok_vr' => {1}<-.
  by exists fd.
Qed.

Lemma compiler_front_endP
  entries
  (p: prog)
  (p': @sprog _pd _ _asmop)
  (gd : pointer)
  scs m mi fn va scs' m' vr :
  compiler_front_end aparams cparams entries p = ok p' →
  fn \in entries →
  sem_call (dc:=indirect_c) (wsw:= nosubword) p tt scs m fn va scs' m' vr →
  extend_mem_eq m mi gd (sp_globs (p_extra p')) →
  alloc_ok p' fn mi →
  ∃ vr' mi',
    [/\
     List.Forall2 value_uincl vr vr',
     sem_call (dc:=direct_c) p' gd scs mi fn va scs' mi' vr' &
     extend_mem_eq m' mi' gd (sp_globs (p_extra p'))
    ].
Proof.
  rewrite /compiler_front_end;
  t_xrbindP => p1 ok_p1 /check_no_ptrP checked_entries p2 ok_p2 p3.
  rewrite print_sprogP => ok_p3 <- {p'} ok_fn exec_p.
  rewrite (compiler_third_part_meta ok_p3) => m_mi ok_mi.
  assert (ok_mi' : alloc_ok (sip := sip_of_asm_e) p2 fn mi).
  - exact: compiler_third_part_alloc_ok ok_p3 ok_mi.
  have := compiler_first_partP ok_p1 ok_fn exec_p.
  case => {p ok_p1 exec_p} vr1 vr_vr1 exec_p1.
  have gd2 := sp_globs_stack_alloc ok_p2.
  rewrite -gd2 in ok_p2.
  case/sem_call_length: (exec_p1) => fd [] ok_fd size_params size_tyin size_tyout size_res.
  have! [mglob ok_mglob] := (alloc_prog_get_fundef ok_p2).
  move=> /(_ _ _ ok_fd)[] fd' /alloc_fd_checked_sao[] ok_sao_p ok_sao_r ok_fd'.
  move: checked_entries => /(_ _ ok_fn) [] params_noptr return_noptr.
  assert (ok_va : wf_args (sp_globs (p_extra p2)) gd (ao_stack_alloc (stackalloc cparams p1)) m mi fn va va).
  - move: params_noptr ok_sao_p.
    rewrite size_params /wf_args.
    move: (sao_params _); clear.
    elim: va.
    + by case => // _ _; constructor.
    by move => v va ih [] // [] // pa /= /ih{}ih /succn_inj /ih{}ih; constructor.
  have disjoint_va : disjoint_values (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)) va va.
  - rewrite /disjoint_values => i1 pi1 w1 i2 pi2 w2.
    by rewrite (allNone_nth _ params_noptr).
  have := alloc_progP _ (hap_hsap haparams) ok_p2 exec_p1 m_mi.
  move => /(_ (hap_hshp haparams) va ok_va disjoint_va ok_mi').
  case => mi' [] vr2 [] exec_p2 [] m'_mi' [] ok_vr2 ?.
  have [] := compiler_third_partP ok_p3.
  case/(_ _ _ _ _ _ _ _ _ ok_fn exec_p2) => vr3 vr2_vr3 exec_p3.
  exists vr3, mi'; split.
  - apply: (Forall2_trans value_uincl_trans); first exact vr_vr1.
    apply: (Forall2_trans value_uincl_trans); last exact vr2_vr3.
    suff -> : vr1 = vr2 by exact: List_Forall2_refl.
    move: ok_sao_r ok_vr2 return_noptr.
    rewrite /wf_results size_res.
    move: (sao_return _); clear.
    elim: vr1 vr2.
    + by case => // ??[] // _ /List_Forall3_inv.
    move => r vr ih vr2 [] // [] // ns /= /succn_inj /ih{}ih /List_Forall3_inv.
    by case: vr2 => // r2 vr2 [] /= -> /ih{}ih /ih ->.
  - exact: exec_p3.
  exact: m'_mi'.
Qed.

Lemma compiler_back_end_meta entries (p: sprog) (tp: lprog) :
  compiler_back_end aparams cparams entries p = ok tp →
  [/\
     lp_rip tp = p.(p_extra).(sp_rip),
     lp_rsp tp = p.(p_extra).(sp_rsp) &
     lp_globs tp = p.(p_extra).(sp_globs)
  ].
Proof.
  rewrite /compiler_back_end; t_xrbindP => _ _ lp ok_lp.
  rewrite print_linearP => zp ok_zp.
  rewrite print_linearP => tp' ok_tp.
  rewrite print_linearP => ?; subst tp'.
  have! [<- [<- [<- _]]] := (tunnel_program_invariants ok_tp).
  have! [<- <- <-] := (stack_zeroization_lprog_invariants ok_zp).
  split.
  - exact: lp_ripE ok_lp.
  - exact: lp_rspE ok_lp.
  exact: lp_globsE ok_lp.
Qed.

Lemma compiler_back_end_to_asm_meta entries (p : sprog) (xp : asm_prog) :
  compiler_back_end_to_asm aparams cparams entries p = ok xp
  -> asm_globs xp = (sp_globs (p_extra p)).
Proof.
  rewrite /compiler_back_end_to_asm.
  t_xrbindP=> tp /compiler_back_end_meta[] _ _ <-.
  by move=> /assemble_progP [_ <-].
Qed.

(* The memory has an allocated stack region that is large enough to hold the local variables of the function and all functions it may call.
  The stack region is described by two pointers: [top-stack m] at the bottom and [root] (held in RSP) at the top
 *)
Definition enough_stack_space
  (xp : asm_prog) (fn : funname) (root : pointer) (m : mem) : Prop :=
  forall fd : asm_fundef,
    get_fundef xp.(asm_funcs) fn = Some fd
    -> let stk_sz := (wunsigned root - wunsigned (top_stack m))%Z in
       (0 <= asm_fd_total_stack fd <= stk_sz)%Z.

Lemma enough_stack_space_alloc_ok
  entries (sp : sprog) (xp : asm_prog) (fn : funname) (m m' : mem) :
  compiler_back_end_to_asm aparams cparams entries sp = ok xp
  -> fn \in entries
  -> (wunsigned (stack_limit m) <= wunsigned (top_stack m'))%Z
  -> enough_stack_space xp fn (top_stack m) m'
  -> alloc_ok sp fn m.
Proof.
  rewrite /compiler_back_end_to_asm /compiler_back_end.
  t_xrbindP => ? /allMP ok_export _ lp ok_lp.
  rewrite print_linearP => zp ok_zp.
  rewrite print_linearP => tp ok_tp.
  rewrite print_linearP => <- ok_xp /InP ok_fn M S.
  move => fd get_fd.
  move: ok_export => /(_ _ ok_fn); rewrite get_fd => /assertP export.
  split; last by rewrite export.
  have! get_lfd := (get_fundef_p' ok_lp get_fd).
  have! [zfd ok_zfd get_zfd] := (stack_zeroization_lprog_get_fundef ok_zp get_lfd).
  have! get_tfd := (get_fundef_tunnel_program ok_tp get_zfd).
  have! [fd' get_fd'] := (ok_get_fundef ok_xp get_tfd).
  case/assemble_fdI => _ _ [] ? [] ? [] ? [] _ _ _ ? _; subst fd'.
  move: get_fd' => /S /=.
  rewrite /lfd_total_stack /=.
  have [ _ <- _ _ _ _ <- _ <- _] /= := stack_zeroization_lfd_invariants ok_zfd.
  rewrite /allocatable_stack /sf_total_stack export.
  move: (wunsigned (stack_limit m)) (wunsigned (top_stack m)) (wunsigned (top_stack m')) M => L T T'.
  Lia.lia.
Qed.

Import sem_one_varmap.

Lemma compiler_back_endP
  entries
  (p : @sprog _pd _ _asmop)
  (tp : lprog)
  (rip : word Uptr)
  (scs : syscall_state)
  (m : mem)
  (scs' : syscall_state)
  (m' : mem)
  (fn : funname)
  args
  res :
  compiler_back_end aparams cparams entries p = ok tp →
  fn \in entries →
  psem.sem_call (dc:= direct_c) p rip scs m fn args scs' m' res →
  ∃ fd : lfundef,
    [/\
      get_fundef tp.(lp_funcs) fn = Some fd,
      fd.(lfd_export) &
      ∀ lm vm,
        vm.[vid tp.(lp_rsp)] = Vword (top_stack m) →
        match_mem m lm →
        List.Forall2 value_uincl args (map (λ x : var_i, vm.[x]) fd.(lfd_arg)) →
        vm.[vid tp.(lp_rip)] = Vword rip →
        vm_initialized_on vm (lfd_callee_saved fd) →
        allocatable_stack m (lfd_total_stack fd) ->
        ∃ vm' lm',
          [/\
            lsem_exportcall tp scs lm fn vm scs' lm' vm',
            match_mem m' lm',
            (cparams.(stack_zero_info) fn <> None ->
              forall p, ~ validw m p U8 ->
                read lm' p U8 = read lm p U8 \/ read lm' p U8 = ok 0%R) &
            List.Forall2 value_uincl res (map (λ x : var_i, vm'.[x]) fd.(lfd_res))
          ]
      ].
Proof.
  rewrite /compiler_back_end; t_xrbindP => ok_export checked_p lp ok_lp.
  rewrite print_linearP => zp ok_zp.
  rewrite print_linearP => tp' ok_tp.
  rewrite print_linearP => ?; subst tp'.
  move=> /InP ok_fn exec_p.
  set vtmp := var_tmps aparams.
  have vtmp_not_magic : disjoint vtmp (magic_variables p).
  - by apply: (var_tmp_not_magic checked_p).
  have p_call :
    sem_export_call p vtmp rip scs m fn args scs' m' res.
  - apply: (merge_varmaps_export_callP checked_p _ exec_p).
    move/allMP: ok_export => /(_ _ ok_fn).
    rewrite /is_export.
    case: get_fundef => // fd /assertP /is_RAnoneP Export.
    by exists fd.
  have :=
    linear_exportcallP
      (hap_hlip haparams)
      vtmp_not_magic
      ok_lp
      p_call.
  case => fd [] lfd [] get_fd get_lfd Export lp_call.
  have! [zfd ok_zfd get_zfd] := (stack_zeroization_lprog_get_fundef ok_zp get_lfd).
  exists (tunneling.tunnel_lfundef fn zfd).
  rewrite /lfd_total_stack /=.
  have [_ <- _ <- _ <- <- <- <- _] := stack_zeroization_lfd_invariants ok_zfd.
  rewrite Export.
  split=> //.
  - exact: get_fundef_tunnel_program ok_tp get_zfd.
  move=> tm tvm H0 H1 H3 H4 H5 H6.
  have H2 := get_var_is_allow_undefined tvm (lfd_arg lfd).
  have {lp_call} := lp_call tm tvm _ _ H1 H2 H3 _ H5.
  have! [-> -> _] := (stack_zeroization_lprog_invariants ok_zp).
  have! [-> [-> _]] := (tunnel_program_invariants ok_tp).
  have /= H6': (sf_stk_max (f_extra fd) + wsize_size (sf_align (f_extra fd)) - 1 <= wunsigned (top_stack m))%Z.
  + move: H6; rewrite /allocatable_stack.
    have := [elaborate (get_fundef_p' ok_lp get_fd)].
    rewrite get_lfd => -[->] /=.
    have /= := [elaborate (wunsigned_range (stack_limit m))].
    by Lia.lia.
  move => /(_ H0 H4 H6') [] vm' [] lm' [] res' [] lp_call ok_rsp' M' U'.
  rewrite get_var_is_allow_undefined => -[] <- res_res'.
  have ok_rsp'' : vm'.[vid (lp_rsp zp)] = Vword (top_stack m).
  + by have! [_ [-> _]] := (tunnel_program_invariants ok_tp).
  have /= H6'':
    (lfd_stk_max lfd + wsize_size (lfd_align lfd) - 1 <= wunsigned (top_stack m))%Z.
  + have := [elaborate (get_fundef_p' ok_lp get_fd)].
    by rewrite get_lfd => -[->] /=.
  set bottom :=
    (align_word (lfd_align lfd) (top_stack m) - wrepr Uptr (lfd_stk_max lfd))%R.
  have H6''':
    (0 <= wunsigned (align_word (lfd_align lfd) (top_stack m)) - lfd_stk_max lfd < wbase Uptr)%Z.
  + have: (0 <= lfd_stk_max lfd)%Z.
    + have := [elaborate (get_fundef_p' ok_lp get_fd)].
      rewrite get_lfd => -[->] /=.
      have! := (linearization_proof.checked_prog ok_lp get_fd).
      rewrite /check_fd /=; t_xrbindP=> _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
      have := frame_size_bound stk_sz_pos stk_extra_sz_pos.
      by Lia.lia.
    have /= := [elaborate (align_word_range (lfd_align lfd) (top_stack m))].
    have /= := [elaborate (wunsigned_range (top_stack m))].
    by Lia.lia.
  have bottom_instack:
    zbetween
      (stack_limit m) (wunsigned (top_stack m) - wunsigned (stack_limit m))
      bottom (lfd_stk_max lfd).
  + rewrite /bottom /zbetween !zify.
    move: H6; rewrite /allocatable_stack.
    have /= ? := [elaborate (align_word_range (lfd_align lfd) (top_stack m))].
    rewrite wunsigned_sub //.
    by Lia.lia.
  have no_overflow_bottom: no_overflow bottom (lfd_stk_max lfd).
  + move: bottom_instack; rewrite /no_overflow /zbetween !zify.
    have /= := [elaborate (wunsigned_range (top_stack m))].
    by Lia.lia.
  have hvalid: ∀ pr, between bottom (lfd_stk_max lfd) pr U8 → validw tm pr U8.
  + move=> pr /(zbetween_trans bottom_instack).
    rewrite -/(between _ _ _ _) -pointer_range_between => hpr.
    apply H1.(valid_stk).
    apply /pointer_rangeP.
    apply: pointer_range_incl_r hpr.
    exact: top_stack_below_root.
  have [zm' [zvm' [zp_call heqvm hmm]]] :=
    stack_zeroization_lprogP (hap_hszp haparams) ok_zp lp_call ok_rsp''
      get_lfd H6'' hvalid.
  move: hmm; rewrite get_lfd -/bottom => hmm.

  exists zvm', zm'; split; cycle 1.
  - move: hmm.
    case: stack_zero_info => [[szs ows]|] /=; last first.
    + by move=> <-.
    move=> hmm.
    split.
    + move=> pr w ok_w.
      have := M'.(read_incl) ok_w.
      rewrite hmm.(read_untouched) //.
      apply not_between_U8_disjoint_zrange => //.
      move=> /(zbetween_trans bottom_instack).
      rewrite -/(between _ _ _ _) -pointer_range_between => /pointer_rangeP hpr.
      have /negP := (stack_region_is_free hpr); apply.
      rewrite (sem_call_validw_stable_sprog exec_p).
      exact: (readV ok_w).
    + by move=> pr /M'.(valid_incl); rewrite hmm.(valid_eq).
    move=> pr.
    rewrite -hmm.(valid_eq).
    by apply M'.(valid_stk).
  - move: hmm.
    case hszs: stack_zero_info => [[szs ows]|] //= hmm _.
    move=> pr hnvalid.
    case hb: (between bottom (lfd_stk_max lfd) pr U8).
    + by right; rewrite (hmm.(read_zero) hb).
    left.
    rewrite -hmm.(read_untouched); last first.
    + apply not_between_U8_disjoint_zrange => //.
      by apply /negP /negPf.
    rewrite (U' _ hnvalid) //.
    have! := (linearization_proof.checked_prog ok_lp get_fd).
    rewrite /check_fd /=; t_xrbindP=> _ _ ok_stk_sz _ _ _.
    case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
    rewrite /align_top_stack align_top_aligned; cycle 1.
    + by Lia.lia.
    + have := frame_size_bound stk_sz_pos stk_extra_sz_pos.
      have! := (wunsigned_range (top_stack m)).
      have /= := wsize_size_pos (sf_align (f_extra fd)).
      by Lia.lia.
    + move: ok_zfd; rewrite /stack_zeroization_lfd hszs Export /=.
      case: ZltP => [_|hle0].
      + rewrite /stack_zeroization_lfd_body; t_xrbindP=> halign _ _ _ _ _.
        move: Export halign.
        have := [elaborate (get_fundef_p' ok_lp get_fd)].
        rewrite get_lfd => -[->] /=.
        by rewrite /frame_size => ->.
      move=> _.
      have -> //: (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) = 0)%Z.
      move: Export stk_frame_le_max hle0.
      have := [elaborate (get_fundef_p' ok_lp get_fd)].
      rewrite get_lfd => -[->] /=.
      rewrite /frame_size => ->.
      by Lia.lia.
    rewrite pointer_range_between.
    move/negP: hb H6'''; rewrite /bottom.
    have := [elaborate (get_fundef_p' ok_lp get_fd)].
    rewrite get_lfd => -[->] /= hb H6'''.
    rewrite wunsigned_sub //.
    by rewrite Z.sub_add_distr Z.sub_diag Z.sub_0_l Z.opp_involutive.
  - have <- //: [seq vm'.[x.(v_var)] | x <- lfd_res lfd]
                = [seq zvm'.[x.(v_var)] | x <- lfd_res lfd].
    apply map_ext.
    move=> x hin; apply heqvm.
    apply /sv_of_listP /in_map.
    by exists x.

  clear -zp_call ok_tp.
  case: zp_call => zfd get_zfd Export zp_exec ok_callee_saved.
  exists (tunneling.tunnel_lfundef fn zfd).
  - exact: get_fundef_tunnel_program ok_tp get_zfd.
  - exact: Export.
  have! [|] := (lsem_run_tunnel_program ok_tp zp_exec).
  - by exists zfd.
  - move => tp_exec _.
    rewrite /ls_export_final size_tunnel_lcmd.
    exact: tp_exec.
  exact: ok_callee_saved.
Qed.

Lemma compiler_back_end_to_asmP
  entries
  (p : @sprog _pd _ _asmop)
  (xp : asm_prog)
  (rip : word Uptr)
  scs (m : mem) scs' (m' : mem)
  (fn: funname)
  args
  res :
  compiler_back_end_to_asm aparams cparams entries p = ok xp
  -> fn \in entries
  -> psem.sem_call (dc:=direct_c) p rip scs m fn args scs' m' res
  -> exists xd : asm_fundef,
      [/\ get_fundef (asm_funcs xp) fn = Some xd
        , asm_fd_export xd
        & forall xm,
               xm.(asm_scs) = scs
            -> xm.(asm_rip) = rip
            -> asm_reg xm ad_rsp = top_stack m
            -> match_mem m xm.(asm_mem)
            -> List.Forall2 value_uincl args (get_typed_reg_values xm xd.(asm_fd_arg))
            -> allocatable_stack m xd.(asm_fd_total_stack)
            -> exists xm',
                [/\ asmsem_exportcall xp fn xm xm'
                  , match_mem m' xm'.(asm_mem), xm'.(asm_scs) = scs'
                  , (cparams.(stack_zero_info) fn <> None ->
                      forall p, ~ validw m p U8 ->
                       read xm'.(asm_mem) p U8 = read xm.(asm_mem) p U8
                       \/ read xm'.(asm_mem) p U8 = ok 0%R)
                  & List.Forall2 value_uincl res (get_typed_reg_values xm' xd.(asm_fd_res))
                ]
      ].
Proof.
  rewrite /compiler_back_end_to_asm.
  t_xrbindP=> lp ok_lp ok_xp.
  move=> ok_fn p_call.
  have [fd [] ok_fd fd_export lp_call] := compiler_back_endP ok_lp ok_fn p_call.
  have [xd ->] := ok_get_fundef ok_xp ok_fd.
  have [disj_rip ok_lp_rsp ok_globs get_xfun] := assemble_progP ok_xp.
  case/assemble_fdI =>
    rsp_not_arg /allP ok_callee_saved
    [] xbody
    [] xargs
    [] xres
    [] ok_xbody ok_xargs ok_xres
    -> {xd}.
  eexists; split; first reflexivity.
  - by rewrite fd_export.
  move=> xm ok_scs ok_rip ok_rsp M /= ok_args hallocatable.

  set s :=
    estate_of_asm_mem
      (top_stack m)
      (lp_rip lp)
      (lp_rsp lp)
      xm.

  assert (LM :=
    lom_eqv_estate_of_asm_mem
      (top_stack m)
      (lp_rsp lp)
      xm
      disj_rip).

  assert (XM :=
    get_var_vmap_of_asm_mem
      (top_stack m)
      (lp_rip lp)
      (lp_rsp lp)
      xm).

  have := lp_call _ _ _ M.
  move=> /(_ (vmap_of_asm_mem (top_stack m) (lp_rip lp) (lp_rsp lp) xm)).
  case.
  - assert (Hrsp := XM (ARReg ad_rsp)).
    move: Hrsp.
    by rewrite /= /to_var /= ok_lp_rsp /rtype /= ok_rsp.
  - have -> //:
      [seq (vmap_of_asm_mem (top_stack m) (lp_rip lp) (lp_rsp lp) xm).[v_var x] | x <- lfd_arg fd] =
      (get_typed_reg_values xm xargs).
    elim: (lfd_arg fd) (xargs) ok_xargs => //= [ | [x ?] xs hrec]; t_xrbindP; first by move=> _ <-.
    by move=> ?? h ? /hrec -> <- /=; rewrite -XM (asm_typed_reg_of_varI h).
  - case: LM => _ _ Y _ _ _ _.
    by move: Y => /= ->; rewrite ok_rip.
  - move => /=.
    apply/allP => x /ok_callee_saved hin.
    have [r ->]: exists2 r, x = (var_of_asm_typed_reg r) & vtype x != sbool.
    + by move/andP: hin => [->] /is_okP [] r /asm_typed_reg_of_varI ->; exists r.
    rewrite /get_var XM /=.
    by case: r => //= ?; rewrite truncate_word_u.
  - exact: hallocatable.
  move=>
      vm'
      [] lm'
      [] {} lp_call M' hzero res_res'.
  subst scs.
  have :=
    asm_gen_exportcall
      (hap_hagp haparams)
      ok_xp
      lp_call
      _
      LM.
  case.
  - apply/allP => ? /mapP [] r hin ->.
    rewrite /get_var (XM r) /=.
    assert (H:= callee_saved_not_bool); move/allP: H => /(_ _ hin) {hin}.
    by case: r => //= r _; rewrite truncate_word_u.

  move=> xm' xp_call LM'.
  have : List.Forall2 value_uincl res (get_typed_reg_values xm' xres).
  + elim: (lfd_res fd) (xres) ok_xres (res) res_res' => [ | [x ?] xs hrec] //=; t_xrbindP.
    + by move=> ? <- res' h; inversion_clear h => /=.
    move=> ? r h ? /hrec{}hrec <- res' /List_Forall2_inv; case: res' => // v res' [hr /hrec] /=.
    apply/List.Forall2_cons/(value_uincl_trans hr).
    rewrite (asm_typed_reg_of_varI h) /=.
    case: LM' => /= _ _ _ _ R RX X F.
    case: (r) => //=.
  exists xm'; split => //.
  - by case: LM' => /= _ <-.
  - by case: LM' => <-.
  move=> hszs pr hnvalid.
  case: LM' => /= _ <- _ _ _ _ _ _.
  by apply (hzero hszs pr hnvalid).
Qed.

(* Agreement relation between source and target memories.
   Expressed in a way that streamlines the composition of compiler-correctness theorems (front-end and back-end).
  TODO: There might be an equivalent definition that is clearer.
*)

Record mem_agreement_with_ghost (m m': mem) (gd: pointer) (data: seq u8) (ma_ghost: mem) : Prop :=
  { ma_extend_mem_eq : extend_mem_eq m ma_ghost gd data
  ; ma_match_mem : match_mem ma_ghost m'
  ; ma_stack_stable : stack_stable m ma_ghost
  ; ma_stack_range : (wunsigned (stack_limit ma_ghost) <= wunsigned (top_stack m'))%Z
  }.

Definition mem_agreement (m m': mem) (gd: pointer) (data: seq u8) : Prop :=
  ∃ ma_ghost, mem_agreement_with_ghost m m' gd data ma_ghost.

Lemma compile_prog_to_asmP
  entries
  (p : prog)
  (xp : asm_prog)
  scs (m : mem) scs' (m' : mem)
  (fn: funname)
  va
  vr
  xm :
  compile_prog_to_asm aparams cparams entries p = ok xp
  -> fn \in entries
  -> psem.sem_call (dc:= indirect_c) (wsw:=nosubword) p tt scs m fn va scs' m' vr
  -> mem_agreement m (asm_mem xm) (asm_rip xm) (asm_globs xp)
  -> enough_stack_space xp fn (top_stack m) (asm_mem xm)
  -> exists xd : asm_fundef,
      [/\
         get_fundef (asm_funcs xp) fn = Some xd
        , asm_fd_export xd
        &   asm_scs xm = scs
            -> asm_reg xm ad_rsp = top_stack m
            -> List.Forall2 value_uincl va (get_typed_reg_values xm (asm_fd_arg xd))
            -> exists xm',
                [/\ asmsem_exportcall xp fn xm xm'
                  , mem_agreement m' (asm_mem xm') (asm_rip xm') (asm_globs xp), asm_scs xm' = scs'
                  , (cparams.(stack_zero_info) fn <> None ->
                      forall p, ~ validw m p U8 ->
                        read xm'.(asm_mem) p U8 = read xm.(asm_mem) p U8
                        \/ read xm'.(asm_mem) p U8 = ok 0%R)
                  & List.Forall2 value_uincl vr (get_typed_reg_values xm' (asm_fd_res xd))
                ]
      ].
Proof.
  rewrite /compile_prog_to_asm; t_xrbindP => sp ok_sp ok_xp ok_fn p_call [] mi.
  have -> := compiler_back_end_to_asm_meta ok_xp.
  case=> /= mi1 mi2 mi3 mi4.
  rewrite (ss_top_stack mi3).
  move=> /dup[] henough /(enough_stack_space_alloc_ok ok_xp ok_fn mi4) ok_mi.
  have := compiler_front_endP ok_sp ok_fn p_call mi1 ok_mi.
  case => vr' [] mi' [] vr_vr' sp_call m1.
  have := compiler_back_end_to_asmP ok_xp ok_fn sp_call.
  case => xd [] ok_xd export /(_ _ _ erefl _ mi2) xp_call.
  exists xd; split => //.
  move=> ok_scs ok_rsp va_args'.
  have hallocatable: allocatable_stack mi (asm_fd_total_stack xd).
  + rewrite /allocatable_stack.
    by have /= := henough _ ok_xd; Lia.lia.
  have := xp_call ok_scs ok_rsp va_args' hallocatable.
  case => xm' [] {} xp_call m2 ok_scs' hzero vr'_res'.
  exists xm'; split => //;
    last exact: Forall2_trans value_uincl_trans vr_vr' vr'_res'.
  + case: xp_call => _ _ _ /= _ /asmsem_invariantP /= xm_xm' _.
    exists mi'; split.
    - rewrite -(asmsem_invariant_rip xm_xm').
      exact: m1.
    - exact: m2.
    - transitivity mi;
        last exact: (sem_call_stack_stable_sprog sp_call).
      transitivity m; last exact: mi3.
      symmetry. exact: (sem_call_stack_stable_uprog p_call).
    rewrite
      -(ss_limit (sem_call_stack_stable_sprog sp_call))
      -(ss_top_stack (asmsem_invariant_stack_stable xm_xm')).
    exact: mi4.
  move=> hszs pr hnvalid.
  have := mi1.(eme_valid) pr.
  case: (@idP (between _ _ _ _)) => [hb|_].
  + move=> _; left.
    have [i [hi ->]]:
      exists i,
        (0 <= i < (Z.of_nat (size (sp_globs (p_extra sp)))))%Z
        /\ (pr = asm_rip xm + wrepr _ i)%R.
    + exists (wunsigned pr - wunsigned (asm_rip xm))%Z; split; last first.
      + rewrite wrepr_sub !wrepr_unsigned.
        by rewrite GRing.addrC GRing.subrK.
      move: hb; rewrite /between /zbetween wsize8 !zify /=.
      by Lia.lia.
    have /mi2.(read_incl) -> := mi1.(eme_read_new) hi.
    by have /m2.(read_incl) -> := m1.(eme_read_new) hi.
  rewrite orbF => hvalideq.
  apply (hzero hszs pr).
  by rewrite -hvalideq.
Qed.

End PROOF.
