From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import fintype finfun ssralg.
Require Import Uint63.

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
  apply: compose_pass.
  - move=> vr'.
    have! h :=
      (lower_slh_prog_sem_call
         (dc := direct_c) (ev := tt) (hap_hshp haparams) ok_pp).
    apply h => //.
  apply: compose_pass_uincl.
  - move=> vr'; apply: (pi_callP (sCP := sCP_unit) ok_pj va_refl).
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
  apply: compose_pass; first by move => vr'; exact: psem_call_u.
  exists vr => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
Qed.

Lemma compiler_third_partP returned_params (p p' : @sprog _pd _ _asmop) :
  compiler_third_part aparams cparams returned_params p = ok p' →
  [/\
    ∀ fn (gd: pointer) scs m va scs' m' vr,
      sem_call (dc:= direct_c) p gd scs m fn va scs' m' vr →
      exists2 vr',
      let rminfo fn :=
        match returned_params fn with
        | Some l =>
          let l' := map (fun i => if i is None then true else false) l in
          if all (fun b => b) l' then None else Some l' (* do we want that? *)
        | None => removereturn cparams p fn
        end
      in
      List.Forall2 value_uincl (fn_keep_only rminfo fn vr) vr' &
      sem_call (dc:= direct_c) p' gd scs m fn va scs' m' vr' &
    ∀ fn m,
      alloc_ok p' fn m → alloc_ok p fn m
  ].
Proof.
  rewrite /compiler_third_part; t_xrbindP=> pa ok_pa.
  rewrite !print_sprogP => ok_pb pc ok_pc.
  rewrite print_sprogP => <- {p'}.
  split.
  + move => fn gd scs m va scs' m' vr exec_p.
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
    by exists vr'.
  rewrite /alloc_ok => fn m alloc_pc fd get_fd.
  have [fda ok_fda get_fda] := [elaborate
    (dead_code_prog_tokeep_get_fundef ok_pa get_fd)].
  have [fdb [get_fdb ok_fdb]] :=
    allocation_proof.all_checked (sip := sip_of_asm_e) ok_pb get_fda.
  have [fdc ok_fdc get_fdc] := [elaborate
    (dead_code_prog_tokeep_get_fundef ok_pc get_fdb)].
  move: (alloc_pc _ get_fdc).
  have [_ _ ->]:= dead_code_fd_meta ok_fdc.
  rewrite /sf_total_stack.
  have [ <- <- <- ] := [elaborate @check_fundef_meta _ _ _ _ _ _ _ (_, fda) _ _ _ ok_fdb].
  have [_ _ ->]:= dead_code_fd_meta ok_fda.
  done.
Qed.

Lemma compiler_third_part_meta entries (p p' : sprog) :
  compiler_third_part aparams cparams entries p = ok p' →
  p_extra p' = p_extra p.
Proof.
  rewrite /compiler_third_part.
  t_xrbindP => pa hpa _ pb hpb.
  have! [_ ok_pa] := (dead_code_prog_tokeep_meta hpa).
  have! [] := (dead_code_prog_tokeep_meta hpb).
  rewrite !print_sprogP /= => _ ok_pb <- {p'}.
  by rewrite ok_pb ok_pa.
Qed.

Lemma compiler_third_part_invariants entries p p' :
  compiler_third_part aparams cparams entries p = ok p' ->
  forall fn fd, get_fundef p.(p_funcs) fn = Some fd ->
  exists fd', get_fundef p'.(p_funcs) fn = Some fd' /\
  fd.(f_extra).(sf_align_args) = fd'.(f_extra).(sf_align_args).
Proof.
  rewrite /compiler_third_part.
  t_xrbindP => pa hpa.
  rewrite 2!print_sprogP /= => check_pa pb hpb.
  rewrite print_sprogP => <-{p'}.
  move=> fn fd ok_fd.
  have [fda ok_fda get_fda] := [elaborate
    dead_code_prog_tokeep_get_fundef hpa ok_fd].
  rewrite /check_sprog in check_pa.
  have [fda' [get_fda' check_fda']] := [elaborate
    allocation_proof.all_checked (pT:=progStack)
      (p2:={| p_funcs := regalloc cparams (p_funcs pa); p_globs := p_globs pa; p_extra := p_extra pa |})
      check_pa get_fda].
  have [fdb ok_fdb get_fdb] := [elaborate
    dead_code_prog_tokeep_get_fundef hpb get_fda'].
  exists fdb; split=> //.
  have [_ _ ->] := dead_code_fd_meta ok_fdb.
  have /= [_ _ _ <-] := [elaborate check_fundef_meta check_fda'].
  have [_ _ ->] := dead_code_fd_meta ok_fda.
  done.
Qed.

(* TODO: move *)
Remark sp_globs_stack_alloc rip rsp data ga la (p: uprog) (p': sprog) :
  alloc_prog (ap_shp aparams) (ap_sap aparams) (fresh_var_ident cparams (Reg (Normal, Direct)) dummy_instr_info 0) rip rsp data ga la p = ok p' →
  sp_globs (p_extra p') = data.
Proof.
  by rewrite /alloc_prog; t_xrbindP => ???? _ <-.
Qed.

Lemma compiler_third_part_alloc_ok entries (p p' : sprog) (fn: funname) (m: mem) :
  compiler_third_part aparams cparams entries p = ok p' →
  alloc_ok p' fn m →
  alloc_ok p fn m.
Proof. case/compiler_third_partP => _; exact. Qed.

Lemma allNone_nth {A} (m: seq (option A)) i :
  allNone m ->
  nth None m i = None.
Proof.
  elim: m i.
  - by move => ? _; exact: nth_nil.
  by case => // m ih [].
Qed.

Lemma check_wf_ptrP entries p ao fn fd :
  check_wf_ptr entries p ao = ok tt ->
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  all2 (λ (x : var_i) pi, wptr_status x == omap pp_writable pi)
    (f_params fd) (sao_params (ao fn)) /\
  let n := find (fun x => wptr_status x != Some true) fd.(f_params) in
  sao_return (ao fn) = [seq Some i | i <- iota 0 n] ++ nseq (size (sao_return (ao fn)) - n) None.
Proof.
  move=> hcheck /InP ok_fn get_fd.
  set n := find (fun x => wptr_status x != Some true) fd.(f_params).
  move: hcheck; rewrite /check_wf_ptr.
  t_xrbindP=> /allMP -/(_ _ ok_fn); rewrite get_fd => /assertP hparams.
  move=> /allMP -/(_ _ ok_fn); rewrite get_fd -/n => /assertP /andP [/eqP hl hr].
  split=> //.
  rewrite -{1}(cat_take_drop n (sao_return _)).
  apply f_equal2 => //.
  apply (@eq_from_nth _ None).
  + by rewrite size_drop size_nseq.
  move=> i; rewrite size_drop => hi.
  rewrite nth_nseq hi.
  exact: allNone_nth hr.
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

Lemma keep_only_false {A} (l : seq A) n :
  size l <= n ->
  keep_only l (nseq n false) = [::].
Proof. by elim: n l => [|n ih] [|a l] //= /ih. Qed.

Lemma keep_only_true {A} (l : seq A) n :
  keep_only l (nseq n true) = l.
Proof. by elim: n l => [//|n ih] [//|a l] /=; rewrite ih. Qed.

Lemma keep_only_cat {A} (l1 l2 : seq A) (tokeep1 tokeep2 : seq bool) :
  size l1 = size tokeep1 ->
  keep_only (l1 ++ l2) (tokeep1 ++ tokeep2) =
  keep_only l1 tokeep1 ++ keep_only l2 tokeep2.
Proof. by elim: tokeep1 l1 => [|b tokeep1 ih] [|a1 l1] //= [] /ih ->; case: b. Qed.

Definition value_uincl_or_in_mem {A} (m : mem) (o : option A) (v v' : value) :=
  match o with
  | None => value_uincl v v'
  | Some _ => value_in_mem m v v'
  end.

Definition size_glob (p:sprog) := Z.of_nat (size (sp_globs (p_extra p))).
Definition get_wptrs (p:uprog) fn :=
  oapp (fun fd => map wptr_status fd.(f_params)) [::] (get_fundef p.(p_funcs) fn).
Definition get_align_args (p:sprog) fn :=
  oapp (fun fd => fd.(f_extra).(sf_align_args)) [::] (get_fundef p.(p_funcs) fn).
Definition get_nb_wptr (p:uprog) fn :=
  find (fun wptr => wptr != Some true) (get_wptrs p fn).

Lemma value_eq_or_in_mem_any_option {A B} (os1 : seq (option A)) (os2 : seq (option B)) m vs vs' :
  List.Forall2 (fun o1 o2 => isSome o1 = isSome o2) os1 os2 ->
  Forall3 (value_eq_or_in_mem m) os1 vs vs' ->
  Forall3 (value_eq_or_in_mem m) os2 vs vs'.
Proof.
  move=> heq heqinmem.
  elim: {os1 os2} heq vs vs' heqinmem.
  move=> [|??] [|??] /List_Forall3_inv //=.
  + by move=> _; constructor.
  move=> o1 o2 os1 os2 heq _ ih [|??] [|??] /List_Forall3_inv // [heqinmem /ih{}ih].
  constructor=> //.
  by case: o1 o2 heq heqinmem => [?|] [?|].
Qed.

Lemma value_uincl_value_in_mem_trans {m} v2 v1 v3 :
  value_uincl v1 v2 -> value_in_mem m v2 v3 -> value_in_mem m v1 v3.
Proof.
  move=> huincl [p [-> hread]].
  exists p; split; first by reflexivity.
  by move=> off w /(value_uincl_get_val_byte huincl); apply hread.
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
  extend_mem m mi gd (sp_globs (p_extra p')) →
  forall va',
  wf_args (size_glob p') gd m mi (get_wptrs p fn) (get_align_args p' fn) va va' ->
  Forall3 (value_eq_or_in_mem mi) (get_wptrs p fn) va va' ->
  alloc_ok p' fn mi →
  ∃ vr' mi', [/\
    sem_call (dc:=direct_c) p' gd scs mi fn va' scs' mi' vr',
    extend_mem m' mi' gd (sp_globs (p_extra p')),
    let n := get_nb_wptr p fn in
      List.Forall2 (value_in_mem mi') (take n vr) (take n va') /\
      List.Forall2 value_uincl (drop n vr) vr' &
    mem_unchanged_params m mi mi' (get_wptrs p fn) va va'
  ].
Proof.
  rewrite /compiler_front_end;
  t_xrbindP => p1 ok_p1 check_p1 p2 ok_p2 p3.
  rewrite print_sprogP => ok_p3 <- {p'} ok_fn exec_p.
  rewrite /size_glob (compiler_third_part_meta ok_p3) -/(size_glob _)
    => m_mi va' va'_wf va'_eqinmem ok_mi.
  have ok_mi': [elaborate alloc_ok p2 fn mi].
  + exact: compiler_third_part_alloc_ok ok_p3 ok_mi.
  have [vr1 vr_vr1 exec_p1] := compiler_first_partP ok_p1 ok_fn exec_p.
  have gd2 := sp_globs_stack_alloc ok_p2.
  rewrite -gd2 in ok_p2.
  case/sem_call_length: (exec_p1) => fd1 [] get_fd1 size_params size_tyin size_tyout size_res.
  have! [mglob ok_mglob] := (alloc_prog_get_fundef ok_p2).
  move=> /(_ _ _ get_fd1)[] fd2 /dup[] ok_fd2 /alloc_fd_checked_sao[] ok_sao_p ok_sao_r get_fd2.
  have [fd [get_fd _]] := sem_callE exec_p.
  rewrite /get_nb_wptr /get_wptrs get_fd /= seq.find_map /preim.
  set n := find _ _.
  have := check_wf_ptrP check_p1 ok_fn get_fd.
  rewrite -/n /= => -[check_params check_return].
  move: check_params; rewrite all2_map -eqseq_all => /eqP check_params.
  rewrite check_params.

  have hargs: [elaborate
    wf_args (size_glob p2) gd m mi
      (map (omap pp_writable) (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)))
      (map (oapp pp_align U8) (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)))
      va va'].
  + move: va'_wf; rewrite /get_wptrs get_fd /= check_params.
    have [fd3 [get_fd3 align_eq]] := compiler_third_part_invariants ok_p3 get_fd2.
    rewrite /get_align_args get_fd3 /= -align_eq.
    move: ok_fd2; rewrite /alloc_fd.
    by t_xrbindP=> _ _ <- /=.

  have heqinmem:
    Forall3 (value_eq_or_in_mem mi)
      (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)) va va'.
  + move: va'_eqinmem; rewrite /get_wptrs get_fd /=.
    apply: value_eq_or_in_mem_any_option.
    rewrite check_params.
    have /Forall2_flip :=
      map_Forall2 (omap pp_writable)
        (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)).
    apply Forall2_impl.
    by move=> _ ? <-; apply isSome_omap.

  have := alloc_progP _ (hap_hsap haparams) ok_p2 exec_p1 m_mi.
  move => /(_ (hap_hshp haparams) va' hargs heqinmem ok_mi').
  case => mi' [] vr2 [] exec_p2 m'_mi' vr2_wf vr2_eqinmem U.
  have [] := compiler_third_partP ok_p3.
  case/(_ _ _ _ _ _ _ _ _ exec_p2).
  set rminfo := fun fn => _.
  move=> /= vr3 vr2_vr3 exec_p3 _.
  exists vr3, mi'; split=> //.

  have hle1: n <= size fd.(f_params) by apply find_size.
  have [/esym size_vr1 /esym size_vr2] := Forall3_size vr2_wf.
  have size_vr := Forall2_size vr_vr1.
  have [/esym size_va /esym size_va'] := Forall3_size heqinmem.
  have /(f_equal size) := check_params; rewrite 2!size_map => /esym size_sao_params.
  have hle2: n <= size vr.
  + have /(f_equal size) := check_return.
    rewrite size_cat size_map size_iota -size_vr1 -size_vr => ->.
    exact: leq_addr.

  (* [vr2_eqinmem] can be split into two thanks to [check_results]:
     - the first [n] elements satisfy [value_in_mem];
     - the other ones satisfy equality. *)
  have [vr2_inmem vr2_eq]:
    List.Forall2 (value_in_mem mi') (take n vr1) (take n vr2) /\ drop n vr1 = drop n vr2.
  + split.
    + apply (nth_Forall2 (Vbool true) (Vbool true)).
      + rewrite size_takel; last by rewrite -size_vr.
        rewrite size_takel; last by rewrite size_vr2 -size_vr1 -size_vr.
        reflexivity.
      rewrite size_takel; last by rewrite -size_vr.
      move=> i hi.
      rewrite nth_take // nth_take //.
      have := Forall3_nth vr2_eqinmem None (Vbool true) (Vbool true).
      rewrite -size_vr1 -size_vr => /(_ _ (leq_trans hi hle2)).
      rewrite check_return nth_cat size_map size_iota hi (nth_map 0);
        last by rewrite size_iota.
      by rewrite nth_iota.
    apply (eq_from_nth (x0 := Vbool true)).
    + by rewrite 2!size_drop size_vr1 size_vr2.
    move=> i; rewrite size_drop -size_vr ltn_subRL => hi.
    rewrite 2!nth_drop.
    have := Forall3_nth vr2_eqinmem None (Vbool true) (Vbool true).
    rewrite -size_vr1 -size_vr => /(_ _ hi).
    rewrite check_return nth_cat size_map size_iota lt_nm_n.
    by rewrite nth_nseq (ltn_sub2rE _ (leq_addr _ _)) -size_vr1 -size_vr hi.

  (* [vr2_wf] can be rewritten into an equality thanks to [check_results] *)
  have {}vr2_wf: take n vr2 = take n va'.
  + apply (eq_from_nth (x0 := Vbool true)).
    + rewrite size_takel; last by rewrite size_vr2 -size_vr1 -size_vr.
      rewrite size_takel; last by rewrite size_va' size_sao_params.
      reflexivity.
    rewrite size_takel; last by rewrite size_vr2 -size_vr1 -size_vr.
    move=> i hi.
    rewrite nth_take // nth_take //.
    have := Forall3_nth vr2_wf None (Vbool true) (Vbool true).
    rewrite -size_vr1 -size_vr => /(_ _ (leq_trans hi hle2)).
    rewrite check_return nth_cat size_map size_iota hi (nth_map 0);
      last by rewrite size_iota.
    by rewrite nth_iota //; case.

  (* [fn_keep_only rminfo fn] is just [drop] thanks to [check_results] *)
  have rminfo_vr2: fn_keep_only rminfo fn vr2 = drop n vr2.
  + rewrite /fn_keep_only /rminfo ok_fn.
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
    + rewrite size_takel; last by rewrite size_vr2 -size_vr1 -size_vr.
      by rewrite size_nseq.
    rewrite keep_only_false; last first.
    + by rewrite size_take; apply geq_minl.
    by rewrite keep_only_true.

  split.
  + rewrite -vr2_wf.
    by apply (Forall2_trans value_uincl_value_in_mem_trans (Forall2_take vr_vr1 n) vr2_inmem).
  apply: (Forall2_trans value_uincl_trans); first exact (Forall2_drop vr_vr1 n).
  by rewrite vr2_eq -rminfo_vr2.
Qed.

Lemma ptr_eq_wf_args glob_size gd m mi wptrs aligns va1 va2 va' :
  Forall3 (fun o v v' => o <> None -> v = v') wptrs va1 va2 ->
  wf_args glob_size gd m mi wptrs aligns va1 va' ->
  wf_args glob_size gd m mi wptrs aligns va2 va'.
Proof.
  move=> heqs hargs.
  move=> i; move: (hargs i); rewrite /wf_arg.
  case ok_writable: nth => [writable|//].
  move=> [p [-> hargp]].
  exists p; split; first by reflexivity.
  have hi := nth_not_default ok_writable ltac:(discriminate).
  have := Forall3_nth heqs None (Vbool true) (Vbool true) hi;
    rewrite ok_writable => /(_ ltac:(discriminate)) <-.
  case: hargp => halign hover hvalid hfresh hwnglob hdisj.
  split=> //.
  move=> hw j vaj pj neq_ij /isSomeP [writablej ok_writablej] ok_vaj ok_pj.
  apply: (hdisj hw _ _ _ neq_ij _ _ ok_pj).
  + by rewrite ok_writablej.
  have hj := nth_not_default ok_writablej ltac:(discriminate).
  have := Forall3_nth heqs None (Vbool true) (Vbool true) hj;
    rewrite ok_writablej => /(_ ltac:(discriminate)) ->.
  done.
Qed.

Lemma ptr_eq_mem_unchanged_params m1 m2 m3 wptrs vs1 vs2 vs' :
  Forall3 (fun o v v' => o <> None -> v = v') wptrs vs1 vs2 ->
  mem_unchanged_params m1 m2 m3 wptrs vs2 vs' ->
  mem_unchanged_params m1 m2 m3 wptrs vs1 vs'.
Proof.
  move=> heqs hunch p hvalid hnvalid hdisj.
  apply (hunch p hvalid hnvalid).
  elim: {wptrs vs1 vs'} hdisj vs2 heqs {hunch}.
  + move=> [|??] /List_Forall3_inv // _.
    by constructor.
  move=> wptr v1 v' wptrs vs1 vs' hdisj _ ih [|v2 vs2]
    /List_Forall3_inv //= [heq /ih{}ih].
  constructor=> //.
  case: wptr heq hdisj => [writable|//].
  by move=> /(_ ltac:(discriminate)) <-.
Qed.

(* [compiler_front_endP] takes [value_eq_or_in_mem] as an hypothesis. But to call
   the lemma in the context of lemma [compile_prog_to_asmP], we rather need
   [value_uincl_or_in_mem] as an hypothesis. *)
Lemma compiler_front_endP_uincl
  entries
  (p: prog)
  (p': @sprog _pd _ _asmop)
  (gd : pointer)
  scs m mi fn va scs' m' vr :
  compiler_front_end aparams cparams entries p = ok p' →
  fn \in entries →
  sem_call (dc:=indirect_c) (wsw:= nosubword) p tt scs m fn va scs' m' vr →
  extend_mem m mi gd (sp_globs (p_extra p')) →
  forall va',
  wf_args (size_glob p') gd m mi (get_wptrs p fn) (get_align_args p' fn) va va' ->
  Forall3 (value_uincl_or_in_mem mi) (get_wptrs p fn) va va' ->
  alloc_ok p' fn mi →
  ∃ vr' mi', [/\
    sem_call (dc:=direct_c) p' gd scs mi fn va' scs' mi' vr',
    extend_mem m' mi' gd (sp_globs (p_extra p')),
    let n := get_nb_wptr p fn in
      List.Forall2 (value_in_mem mi') (take n vr) (take n va') /\
      List.Forall2 value_uincl (drop n vr) vr' &
    mem_unchanged_params m mi mi' (get_wptrs p fn) va va'
  ].
Proof.
  move=> ok_p' ok_fn exec_p m_mi va' va'_wf va'_uinmem ok_mi.

  (* We define [va2] as [va] where non-reg ptr values are replaced by values
     from [va']. We can prove
     [Forall3 (value_eq_or_in_mem mi) (get_wptrs p fn) va2 va'] and thus
     call [compiler_front_endP] on [va2] and [va']. *)
  set va2 :=
    map3 (fun o v v' => if o is Some _ then v else v') (get_wptrs p fn) va va'.
  have [size_va size_va'] := Forall3_size va'_uinmem.

  have huincl: List.Forall2 value_uincl va va2.
  + elim: {va va' exec_p va'_wf size_va size_va'} va'_uinmem @va2 => /=.
    + by constructor.
    move=> wptr v v' wptrs va va' huinmem _ ih.
    constructor=> //.
    by case: wptr huinmem => [writable|] /=.
  have [vr2 [exec2_p huincl2]] := psem.sem_call_uincl huincl exec_p.

  have hptreq: Forall3 (fun o v v' => o <> None -> v = v') (get_wptrs p fn) va va2.
  + elim: {va va' exec_p va'_wf size_va size_va'} va'_uinmem @va2 {huincl exec2_p} => /=.
    + by constructor.
    move=> wptr v v' wptrs va va' _ _ ih.
    constructor=> //.
    by case: wptr.
  have hargs := ptr_eq_wf_args hptreq va'_wf.

  have heqinmem: Forall3 (value_eq_or_in_mem mi) (get_wptrs p fn) va2 va'.
  + elim: {va va' exec_p va'_wf size_va size_va'} va'_uinmem @va2
      {huincl exec2_p hptreq hargs} => /=.
    + by constructor.
    move=> wptr v v' wptrs va va' huinmem _ ih.
    constructor=> //.
    by case: wptr huinmem => [writable|] /=.

  have [vr' [mi' [p'_call m'_mi' vr2_vr' U]]] :=
    compiler_front_endP ok_p' ok_fn exec2_p m_mi hargs heqinmem ok_mi.

  exists vr', mi'; split=> //.
  + case: vr2_vr' => hres1 hres2.
    split.
    + by apply: Forall2_trans value_uincl_value_in_mem_trans (Forall2_take huincl2 _) hres1.
    by apply: Forall2_trans value_uincl_trans (Forall2_drop huincl2 _) hres2.
  by apply: (ptr_eq_mem_unchanged_params hptreq U).
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
              forall p, ~ validw m Aligned p U8 ->
                read lm' Aligned p U8 = read lm Aligned p U8 \/ read lm' Aligned p U8 = ok 0%R) &
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
  - exact: (var_tmp_not_magic (sip := sip_of_asm_e) checked_p).
  have p_call :
    sem_export_call p vtmp rip scs m fn args scs' m' res.
  - apply: (merge_varmaps_export_callP (sip := sip_of_asm_e) checked_p _ exec_p).
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
  have hvalid: ∀ pr, between bottom (lfd_stk_max lfd) pr U8 → validw tm Aligned pr U8.
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
    + move=> /= pr hb hval.
      have := M'.(read_incl_mem) hb hval.
      rewrite hmm.(read_untouched) //.
      apply not_between_U8_disjoint_zrange => //.
      move=> /(zbetween_trans bottom_instack).
      rewrite -/(between _ _ _ _) -pointer_range_between => /pointer_rangeP.
      have ss := sem_call_stack_stable_sprog exec_p.
      rewrite ss.(ss_limit) (ss_top_stack ss).
      have := [elaborate top_stack_below_root _ m']; rewrite -/(top_stack _) /=.
      by Lia.lia.
    + move=> pr w hb ok_w.
      have := M'.(read_incl_stk) hb ok_w.
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
                      forall p, ~ validw m Aligned p U8 ->
                       read xm'.(asm_mem) Aligned p U8 = read xm.(asm_mem) Aligned p U8
                       \/ read xm'.(asm_mem) Aligned p U8 = ok 0%R)
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
  { ma_extend_mem : extend_mem m ma_ghost gd data
  ; ma_match_mem : match_mem ma_ghost m'
  ; ma_stack_stable : stack_stable m ma_ghost
  ; ma_stack_range : (wunsigned (stack_limit ma_ghost) <= wunsigned (top_stack m'))%Z
  }.

Definition mem_agreement (m m': mem) (gd: pointer) (data: seq u8) : Prop :=
  ∃ ma_ghost, mem_agreement_with_ghost m m' gd data ma_ghost.

Definition get_asm_align_args (xp:asm_prog) fn :=
  oapp (fun xd => xd.(asm_fd_align_args)) [::] (get_fundef xp.(asm_funcs) fn).

Lemma compiler_back_end_to_asm_get_fundef entries sp xp fn :
  compiler_back_end_to_asm aparams cparams entries sp = ok xp ->
  fn \in entries ->
  exists sfd xd, [/\
    get_fundef sp.(p_funcs) fn = Some sfd,
    get_fundef xp.(asm_funcs) fn = Some xd,
    xd.(asm_fd_export) &
    sfd.(f_extra).(sf_align_args) = xd.(asm_fd_align_args)].
Proof.
  move=> ok_xp ok_fn.
  move: ok_xp; rewrite /compiler_back_end_to_asm.
  t_xrbindP=> lp ok_lp ok_xp.
  move: ok_lp; rewrite /compiler_back_end.
  t_xrbindP=> hcheck _ lp1 ok_lp1 lp2.
  rewrite print_linearP => ok_lp2 lp3.
  rewrite print_linearP => ok_lp3.
  rewrite print_linearP => ?; subst lp.

  have [sfd [get_sfd ranone]]:
    exists sfd,
      get_fundef sp.(p_funcs) fn = Some sfd
      /\ is_RAnone sfd.(f_extra).(sf_return_address).
  + move: hcheck; rewrite /check_export.
    have /InP ok_fn' := ok_fn.
    move=> /allMP -/(_ fn ok_fn').
    case: get_fundef => //.
    t_xrbindP=> sfd ranone.
    by exists sfd.

  have get_lfd1 := [elaborate get_fundef_p' ok_lp1 get_sfd].
  have [lfd2 ok_lfd2 get_lfd2] := [elaborate
    stack_zeroization_lprog_get_fundef ok_lp2 get_lfd1].
  have get_lfd3 := [elaborate get_fundef_tunnel_program ok_lp3 get_lfd2].
  have [xd get_xd ok_xd] := [elaborate ok_get_fundef ok_xp get_lfd3].

  exists sfd, xd.
  move/assemble_fdI: ok_xd => [_ _ [_ [_ [_ [_ _ _ {-2}-> _]]]]] /=.
  move/stack_zeroization_lfd_invariants: ok_lfd2 => [_ _ _ _ _ _ <- _ _ [_ <-]] /=.
  by split.
Qed.

(* FIXME: do we want to ensure wf_result_pointer? the only thing that matters is value_mem_uincl, it seems *)
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
  -> forall mi,
     mem_agreement_with_ghost m (asm_mem xm) (asm_rip xm) (asm_globs xp) mi
  -> enough_stack_space xp fn (top_stack m) (asm_mem xm)
  -> exists xd : asm_fundef,
      [/\
         get_fundef (asm_funcs xp) fn = Some xd
        , asm_fd_export xd
        &   asm_scs xm = scs
            -> asm_reg xm ad_rsp = top_stack m
            -> wf_args (Z.of_nat (size (asm_globs xp))) (asm_rip xm) m mi
                (get_wptrs p fn) (get_asm_align_args xp fn) va (get_typed_reg_values xm (asm_fd_arg xd))
            -> Forall3 (value_uincl_or_in_mem (asm_mem xm)) (get_wptrs p fn) va (get_typed_reg_values xm (asm_fd_arg xd))
            -> exists xm',
                [/\ asmsem_exportcall xp fn xm xm'
                  , mem_agreement m' (asm_mem xm') (asm_rip xm') (asm_globs xp), asm_scs xm' = scs'
                  , (cparams.(stack_zero_info) fn <> None ->
                      forall pr, ~ validw m Aligned pr U8 ->
                        Forall3 (disjoint_from_writable_param (ep:=ep_of_asm_e) pr) (get_wptrs p fn) va (get_typed_reg_values xm (asm_fd_arg xd)) ->
                        read xm'.(asm_mem) Aligned pr U8 = read xm.(asm_mem) Aligned pr U8
                        \/ read xm'.(asm_mem) Aligned pr U8 = ok 0%R)
                  & let n := get_nb_wptr p fn in
                    List.Forall2 (value_in_mem (asm_mem xm')) (take n vr) (take n (get_typed_reg_values xm (asm_fd_arg xd))) /\
                    List.Forall2 value_uincl (drop n vr) (get_typed_reg_values xm' (asm_fd_res xd))
                ]
      ].
Proof.
  rewrite /compile_prog_to_asm; t_xrbindP => sp ok_sp ok_xp ok_fn p_call mi.
  have -> := compiler_back_end_to_asm_meta ok_xp.
  case=> /= mi1 mi2 mi3 mi4.
  rewrite (ss_top_stack mi3).
  move=> /dup[] henough /(enough_stack_space_alloc_ok ok_xp ok_fn mi4) ok_mi.
  have [sfd [xd [get_sfd get_xd xd_export align_args_eq]]] :=
    compiler_back_end_to_asm_get_fundef ok_xp ok_fn.
  exists xd; split=> //.
  move=> ok_scs ok_rsp va_wf va_uinmem.
  have hargs: [elaborate
    wf_args (size_glob sp) (asm_rip xm) m mi (get_wptrs p fn)
      (get_align_args sp fn) va (get_typed_reg_values xm (asm_fd_arg xd))].
  + rewrite /get_align_args get_sfd /=.
    move: va_wf.
    rewrite /get_asm_align_args get_xd /=.
    by rewrite align_args_eq.
  have huinmem:
    Forall3 (value_uincl_or_in_mem mi) (get_wptrs p fn) va
      (get_typed_reg_values xm (asm_fd_arg xd)).
  + have [hsize1 hsize2] := Forall3_size va_uinmem.
    apply (nth_Forall3 None (Vbool true) (Vbool true)) => // i hi.
    have := Forall3_nth va_uinmem None (Vbool true) (Vbool true) hi.
    case ok_writable: nth => [writable|//].
    move=> [pr [ok_pr hread]]; rewrite ok_pr.
    exists pr; split; first by reflexivity.
    move=> off w /[dup] /get_val_byte_bound hoff /hread ok_w.
    move: (va_wf i); rewrite /wf_arg ok_writable ok_pr.
    move=> [_ [[<-] hargp]].
    rewrite -ok_w; apply (match_mem_read_incl_mem mi2).
    apply hargp.(wap_valid).
    by apply (between_byte hargp.(wap_no_overflow) (zbetween_refl _ _) hoff).

  have := compiler_front_endP_uincl ok_sp ok_fn p_call mi1 hargs huinmem
    (enough_stack_space_alloc_ok ok_xp ok_fn mi4 henough).
  case => vr' [] mi' [] sp_call m1 vr_vr' U.
  have := compiler_back_end_to_asmP ok_xp ok_fn sp_call.
  rewrite get_xd.
  case => _ [] [<-] _ /(_ _ _ erefl _ mi2) xp_call.
  have hallocatable: allocatable_stack mi (asm_fd_total_stack xd).
  + rewrite /allocatable_stack.
    by have /= := henough _ get_xd; Lia.lia.
  have := xp_call ok_scs ok_rsp (List_Forall2_refl _ value_uincl_refl) hallocatable.
  case => xm' [] {} xp_call m2 ok_scs' hzero vr'_res'.
  exists xm'; split => //.
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
  + move=> hszs pr hnvalid hdisj.
    change reg_size with Uptr in pr.
    case: (@idP (validw mi Aligned pr U8)).
    + move=> hvalid.
      left.
      have := U _ hvalid hnvalid hdisj.
      rewrite (match_mem_read_incl_mem mi2 hvalid).
      rewrite (sem_call_validw_stable_sprog sp_call) in hvalid.
      by rewrite (match_mem_read_incl_mem m2 hvalid).
    move=> hnvalid'.
    by apply hzero.
  split; last first.
  + by apply: (Forall2_trans value_uincl_trans (proj2 vr_vr')).
  move: vr_vr'.
  move=> /= [vr_vr' _].
  apply: Forall2_impl vr_vr'.
  move=> v1 _ [pr [-> hread]].
  exists pr; split; first by reflexivity.
  move=> off w /hread.
  by apply (mm_read_ok m2).
Qed.

End PROOF.
