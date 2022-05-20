From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem psem_facts compiler_util compiler.
Require Import
  allocation
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
  lowering_proof
  tunneling_proof
  linearization_proof
  merge_varmaps_proof
  psem_of_sem_proof.
Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen_proof.
Require Import
  x86_gen_proof
  x86_sem
  x86_linearization_proof
  x86_stack_alloc_proof.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record architecture_hyps (aparams : architecture_params) := mk_ahyps {
  is_move_opP : forall op vx v,
    aparams.(is_move_op) op->
    exec_sopn (Oasm op) [:: vx] = ok v ->
    List.Forall2 value_uincl v [:: vx];
}.

(* Parameters specific to the architecture. *)
Definition mov_ofsP := x86_stack_alloc_proof.x86_mov_ofsP.
Definition hlparams := x86_linearization_proof.h_x86_linearization_params.

Section PROOF.

Variable cparams : compiler_params.
Variable aparams : architecture_params.
Variable ahyps   : architecture_hyps aparams.

Hypothesis print_uprogP : forall s p, cparams.(print_uprog) s p = p.
Hypothesis print_sprogP : forall s p, cparams.(print_sprog) s p = p.
Hypothesis print_linearP : forall s p, cparams.(print_linear) s p = p.

Section IS_MOVE_OP.

Context
  (is_move_op : asm_op_t -> bool)
  (is_move_opP :
    forall op vx v,
      is_move_op op
      -> exec_sopn (Oasm op) [:: vx ] = ok v
      -> List.Forall2 value_uincl v [:: vx ]).

Lemma unroll1P (fn: funname) (p p':uprog) ev mem va va' mem' vr:
  unroll1 is_move_op p = ok p' ->
  sem_call p ev mem fn va mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists2 vr', sem_call p' ev mem fn va' mem' vr' & List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll1=> Heq Hsem Hall.
  have hsemu := unroll_callP Hsem.
  have [vr' [hsemc hall']]:= const_prop_callP hsemu Hall.
  have Hall'' : List.Forall2 value_uincl va' va'. by apply List_Forall2_refl.
  have [vr'' [hsemc' hv]] := dead_code_callPu is_move_opP Heq Hall'' hsemc.
  exists vr'' => //. apply: Forall2_trans hall' hv.
  move=> v1 v2 v3 h1 h2. by apply: value_uincl_trans h1 h2.
Qed.

Lemma unrollP (fn: funname) (p p': prog) ev mem va va' mem' vr:
  unroll is_move_op Loop.nb p = ok p' ->
  sem_call p ev mem  fn va mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call p' ev mem fn va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  elim: Loop.nb p va va' vr => /= [p //|n Hn] p va va' vr.
  apply: rbindP=> z Hz.
  case: ifP=> [_ [] ->|_ Hu Hs Hall].
  + by move=> /sem_call_uincl h/h{h}.
  have [vr' hsem1 hall1]:= unroll1P Hz Hs Hall.
  have [vr'' [hsem2 hall2]]:= Hn _ _ _ _ Hu hsem1 (List_Forall2_refl _ value_uincl_refl).
  exists vr'';split => //.
  by apply: Forall2_trans value_uincl_trans hall1 hall2.
Qed.

End IS_MOVE_OP.

Opaque Loop.nb.

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

Lemma compiler_first_partP entries (p: prog) (p': uprog) m fn va m' vr :
  compiler_first_part cparams aparams entries p = ok p' →
  fn \in entries →
  sem.sem_call p m fn va m' vr →
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    psem.sem_call p' tt m fn va m' vr'.
Proof.
  rewrite /compiler_first_part; t_xrbindP => pa0.
  rewrite print_uprogP => ok_pa0 pa.
  rewrite print_uprogP => ok_pa pb.
  rewrite print_uprogP => ok_pb pc.
  rewrite print_uprogP => ok_pc [].
  rewrite !print_uprogP => ok_pd pe ok_pe.
  rewrite !print_uprogP => pf ok_pf pg.
  rewrite !print_uprogP => ok_pg ph ok_ph _ /assertP.
  rewrite print_uprogP => ok_fvars.
  rewrite print_uprogP => pp ok_pp.
  rewrite print_uprogP => <- {p'} ok_fn exec_p.
  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: compose_pass_uincl; first by move=> vr' Hvr'; apply: (pi_callP (sCP := sCP_unit) ok_pp va_refl); exact Hvr'.
  apply: compose_pass; first by move => vr'; apply: (lower_callP (lowering_opt cparams) (warning cparams) (is_var_in_memory cparams) ok_fvars).
  apply: compose_pass; first by move => vr'; apply: (makeReferenceArguments_callP ok_ph).
  apply: compose_pass; first by move => vr'; apply: (RGP.remove_globP ok_pg).
  apply: compose_pass; first by move=> vr'; apply:(expand_callP ok_pf).
  apply: compose_pass_uincl; first by move =>vr'; apply: (remove_init_fdPu _ va_refl).
  apply: compose_pass_uincl; first by move => vr' Hvr'; apply: (dead_code_callPu ahyps.(is_move_opP) ok_pe va_refl); exact: Hvr'.
  apply: compose_pass_uincl; first by move => vr'; apply: (CheckAllocRegU.alloc_callP ok_pd).
  rewrite surj_prog.
  apply: compose_pass_uincl; first by move => vr' Hvr'; apply: (unrollP ahyps.(is_move_opP) ok_pc _ va_refl); exact: Hvr'.
  apply: compose_pass; first by move => vr'; exact: (dead_calls_err_seqP (sCP:= sCP_unit) ok_pb).
  apply: compose_pass_uincl; first by move => vr' Hvr'; apply: (inline_call_errP ok_pa va_refl); exact: Hvr'.
  apply: compose_pass; first by move => vr'; apply: (add_init_fdP).
  apply: compose_pass_uincl; first by move=> vr' Hvr'; apply: (array_copy_fdP (sCP := sCP_unit) ok_pa0 va_refl); exact Hvr'.
  apply: compose_pass; first by move => vr'; exact: psem_call.
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

Lemma compiler_third_partP entries (p: sprog) (p': sprog) :
  compiler_third_part cparams aparams entries p = ok p' →
  [/\
    ∀ fn (gd: pointer) m va m' vr,
      fn \in entries →
      psem.sem_call p gd m fn va m' vr →
      exists2 vr',
      List.Forall2 value_uincl vr vr' &
      psem.sem_call p' gd m fn va m' vr' &
    ∀ fn m,
      alloc_ok p' fn m → alloc_ok p fn m
  ].
Proof.
  rewrite /compiler_third_part; t_xrbindP.
  move => _ /check_removereturnP ok_rr pa ok_pa [].
  rewrite !print_sprogP => ok_pb pc ok_pc.
  rewrite print_sprogP => <- {p'}.
  split.
  + move => fn gd m va m' vr ok_fn exec_p.
    have va_refl : List.Forall2 value_uincl va va.
    - exact: List_Forall2_refl.
    apply: compose_pass_uincl; first by move => vr' Hvr'; apply: (dead_code_callPs ahyps.(is_move_opP) ok_pc va_refl); exact: Hvr'.
    apply: compose_pass_uincl; first by move => vr'; apply: (CheckAllocRegS.alloc_callP ok_pb).
    rewrite surj_prog.
    have [vr' [exec_pa]]:= dead_code_tokeep_callPs ahyps.(is_move_opP) ok_pa va_refl exec_p.
    rewrite /fn_keep_only (ok_rr _ ok_fn) => vr_vr'.
    by exists vr'.
  rewrite /alloc_ok => fn m alloc_pc fd get_fd.
  have [fda ok_fda get_fda] := dead_code_prog_tokeep_get_fundef ok_pa get_fd.
  have [fdb [get_fdb ok_fdb]] := CheckAllocRegS.all_checked ok_pb get_fda.
  have [fdc ok_fdc get_fdc] := dead_code_prog_tokeep_get_fundef ok_pc get_fdb.
  move: (alloc_pc _ get_fdc).
  have [_ _ ->]:= dead_code_fd_meta ok_fdc.
  have /=[_ _ _ <-] := CheckAllocRegS.check_fundef_meta ok_fdb.
  have [_ _ ->]:= dead_code_fd_meta ok_fda.
  done.
Qed.

Lemma compiler_third_part_meta entries (p p' : sprog) :
  compiler_third_part cparams aparams entries p = ok p' →
  p_extra p' = p_extra p.
Proof.
  rewrite /compiler_third_part; t_xrbindP => _ _ pa /dead_code_prog_tokeep_meta[] _ ok_pa _ _ pb /dead_code_prog_tokeep_meta[].
  rewrite !print_sprogP /= => _ ok_pb <- {p'}.
  by rewrite ok_pb ok_pa.
Qed.

(* TODO: move *)
Remark sp_globs_stack_alloc rip rsp data ga la (p: uprog) (p': sprog) :
  alloc_prog mov_ofs rip rsp data ga la p = ok p' →
  sp_globs (p_extra p') = data.
Proof.
  rewrite /alloc_prog; t_xrbindP => ??.
  do 2 case: ifP => // _.
  by t_xrbindP => ? _ <-.
Qed.

Lemma compiler_third_part_alloc_ok entries (p p' : sprog) (fn: funname) (m: mem) :
  compiler_third_part cparams aparams entries p = ok p' →
  alloc_ok p' fn m →
  alloc_ok p fn m.
Proof. case/compiler_third_partP => _; exact. Qed.

Lemma check_no_ptrP entries ao u fn :
  check_no_ptr entries ao = ok u →
  fn \in entries →
  allNone (sao_params (ao fn)) ∧ allNone (sao_return (ao fn)).
Proof.
  clear.
  case: u => /allMP h ok_fn; move: (h _ ok_fn).
  by t_xrbindP => _ /assertP -> /assertP.
Qed.

Lemma allNone_nth {A} (m: seq (option A)) i :
  allNone m ->
  nth None m i = None.
Proof.
  elim: m i.
  - by move => ? _; exact: nth_nil.
  by case => // m ih [].
Qed.

Lemma sem_call_length (p: uprog) m fn va m' vr :
  sem_call p tt m fn va m' vr →
  ∃ fd,
    [/\ get_fundef (p_funcs p) fn = Some fd,
     size (f_params fd) = size va,
     size (f_tyin fd) = size va,
     size (f_tyout fd) = size vr &
     size (f_res fd) = size vr].
Proof.
  case/sem_callE => fd [] -> [] va' [] ? [] ? [] ? [] vr' [] ok_args [] _ ok_va' _ [] /size_mapM ok_vr' ok_res _.
  have := size_fold2 ok_va'.
  have [<- <-] := size_mapM2 ok_args.
  have [size_vr' <-] := size_mapM2 ok_res.
  rewrite {2}size_vr' -ok_vr' => {1}<-.
  by exists fd.
Qed.

Lemma compiler_front_endP entries subroutines (p: prog) (p': sprog) (gd: pointer) m mi fn va m' vr :
  compiler_front_end cparams aparams entries subroutines p = ok p' →
  fn \in entries →
  sem.sem_call p m fn va m' vr →
  extend_mem m mi gd (sp_globs (p_extra p')) →
  alloc_ok p' fn mi →
  ∃ vr' mi',
    [/\
     List.Forall2 value_uincl vr vr',
     psem.sem_call p' gd mi fn va mi' vr' &
     extend_mem m' mi' gd (sp_globs (p_extra p'))
    ].
Proof.
  rewrite /compiler_front_end; t_xrbindP.
  move => p1 ok_p1 [] /check_no_ptrP checked_entries p2 ok_p2 p3.
  rewrite print_sprogP => ok_p3 <- {p'} ok_fn exec_p.
  rewrite (compiler_third_part_meta ok_p3) => m_mi ok_mi.
  have {ok_mi} ok_mi : alloc_ok p2 fn mi.
  - exact: compiler_third_part_alloc_ok ok_p3 ok_mi.
  have := compiler_first_partP ok_p1 _ exec_p.
  rewrite mem_cat ok_fn => /(_ erefl).
  case => {p ok_p1 exec_p} vr1 vr_vr1 exec_p1.
  have gd2 := sp_globs_stack_alloc ok_p2.
  rewrite -gd2 in ok_p2.
  case/sem_call_length: (exec_p1) => fd [] ok_fd size_params size_tyin size_tyout size_res.
  case/alloc_prog_get_fundef: (ok_p2) => mglob ok_mglob /(_ _ _ ok_fd)[] fd' /alloc_fd_checked_sao[] ok_sao_p ok_sao_r ok_fd'.
  move: checked_entries => /(_ _ ok_fn) [] params_noptr return_noptr.
  have ok_va : wf_args (sp_globs (p_extra p2)) gd (ao_stack_alloc (stackalloc cparams p1)) m mi fn va va.
  - move: params_noptr ok_sao_p.
    rewrite size_params /wf_args.
    move: (sao_params _); clear.
    elim: va.
    + by case => // _ _; constructor.
    by move => v va ih [] // [] // pa /= /ih{}ih /succn_inj /ih{}ih; constructor.
  have disjoint_va : disjoint_values (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)) va va.
  - rewrite /disjoint_values => i1 pi1 w1 i2 pi2 w2.
    by rewrite (allNone_nth _ params_noptr).
  have := alloc_progP mov_ofsP ok_p2 exec_p1 m_mi.
  move => /(_ va ok_va disjoint_va ok_mi).
  case => mi' [] vr2 [] exec_p2 [] m'_mi' [] ok_vr2 ?.
  have [] := compiler_third_partP ok_p3.
  case/(_ _ _ _ _ _ _ ok_fn exec_p2) => vr3 vr2_vr3 exec_p3.
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

Lemma compiler_back_end_meta callee_saved entries (p: sprog) (tp: lprog) :
  compiler_back_end cparams callee_saved entries p = ok tp →
  [/\
     lp_rip tp = p.(p_extra).(sp_rip),
     lp_rsp tp = p.(p_extra).(sp_rsp) &
     lp_globs tp = p.(p_extra).(sp_globs)
  ].
Proof.
  rewrite /compiler_back_end; t_xrbindP => _ _ _ _ lp ok_lp p2.
  rewrite !print_linearP => ok_tp ?; subst p2.
  have [ <- [] <- [] <- _ ] := tunnel_program_invariants ok_tp.
  split.
  - exact: lp_ripE ok_lp.
  - exact: lp_rspE ok_lp.
  exact: lp_globsE ok_lp.
Qed.

Lemma compiler_back_end_to_x86_meta entries (p: sprog) (xp: x86_prog) :
  compiler_back_end_to_x86 cparams entries p = ok xp →
  [/\
    arch_extra.to_var x86_decl.RSP = {| vtype := sword64; vname := p.(p_extra).(sp_rsp) |}
    & asm_globs xp = p.(p_extra).(sp_globs)
  ].
Proof.
  rewrite /compiler_back_end_to_x86.
  t_xrbindP => tp /compiler_back_end_meta[] A B C D.
  have [E F H] := assemble_progP D.
  rewrite /to_var (assemble_prog_RSP D).
  by rewrite -B -C.
Qed.

(* The memory has an allocated stack region that is large enough to hold the local variables of the function and all functions it may call.
  The stack region is described by two pointers: [top-stack m] at the bottom and [root] (held in RSP) at the top
 *)
Definition enough_stack_space (xp: x86_prog) (fn: funname) (root: pointer) (m: mem) : Prop :=
  ∀ fd : x86_fundef,
    get_fundef xp.(asm_funcs) fn = Some fd →
    (0 <= asm_fd_total_stack fd <= wunsigned root - wunsigned (top_stack m))%Z.

Lemma enough_stack_space_alloc_ok entries (sp: sprog) (xp: x86_prog) (fn: funname) (m m': mem) :
  compiler_back_end_to_x86 cparams entries sp = ok xp →
  fn \in entries →
  (wunsigned (stack_limit m) <= wunsigned (top_stack m'))%Z →
  enough_stack_space xp fn (top_stack m) m' →
  alloc_ok sp fn m.
Proof.
  rewrite /compiler_back_end_to_x86 /compiler_back_end.
  t_xrbindP => ? [] /allMP ok_export _ _ lp ok_lp tp.
  rewrite !print_linearP => ok_tp <- ok_xp ok_fn M S.
  move => fd ok_fd.
  move: ok_export => /(_ _ ok_fn); rewrite ok_fd => /assertP /eqP Export.
  split; last by rewrite Export.
  move: ok_fd =>
    /(get_fundef_p' ok_lp)
    /(get_fundef_tunnel_program ok_tp)
    /(ok_get_fundef assemble_progP ok_xp)
    [fd' ok_fd'].
  case/assemble_fdI => _ _ [] ? [] ? [] ? [] _ _ _ ?; subst fd'.
  move: ok_fd' => /S /=.
  rewrite /allocatable_stack.
  move: (wunsigned (stack_limit m)) (wunsigned (top_stack m)) (wunsigned (top_stack m')) M => L T T'.
  Lia.lia.
Qed.

Import sem_one_varmap.
Import x86_linearization.

Lemma compiler_back_endP callee_saved entries (p: sprog) (tp: lprog) (rip: word Uptr) (m m':mem) (fn: funname) args res :
  compiler_back_end cparams callee_saved entries p = ok tp →
  fn \in entries →
  psem.sem_call p rip m fn args m' res →
  ∃ fd : lfundef,
    [/\
      get_fundef tp.(lp_funcs) fn = Some fd,
      fd.(lfd_export) &
      ∀ lm vm args',
        wf_vm vm →
        vm.[vid tp.(lp_rsp)]%vmap = ok (pword_of_word (top_stack m)) →
        match_mem m lm →
        mapM (λ x : var_i, get_var vm x) fd.(lfd_arg) = ok args' →
        List.Forall2 value_uincl args args' →
        vm.[vid tp.(lp_rip)]%vmap = ok (pword_of_word rip) →
        vm_initialized_on vm ((vid (lp_tmp lparams) : var) :: lfd_callee_saved fd) →
        all2 check_ty_val fd.(lfd_tyin) args' ∧
        ∃ vm' lm' res',
          [/\
            lsem_exportcall tp callee_saved lm fn vm lm' vm',
            match_mem m' lm',
            mapM (λ x : var_i, get_var vm' x) fd.(lfd_res) = ok res',
            List.Forall2 value_uincl res res' &
            all2 check_ty_val fd.(lfd_tyout) res'
          ]
      ].
Proof.
  rewrite /compiler_back_end; t_xrbindP => - [] ok_export [] checked_p lp ok_lp tp'.
  rewrite !print_linearP => ok_tp ? ok_fn exec_p; subst tp'.
  have lp_tmp_not_magic : ~~ Sv.mem (vid (lp_tmp x86_linearization_params)) (magic_variables p).
  - apply/Sv_memP; exact: var_tmp_not_magic checked_p.
  have p_call : sem_export_call p (extra_free_registers cparams) (vid (lp_tmp x86_linearization_params)) callee_saved rip m fn args m' res.
  - apply: (merge_varmaps_export_callP checked_p _ exec_p).
    move/allMP: ok_export => /(_ _ ok_fn).
    rewrite /is_export.
    case: get_fundef => // fd /assertP /eqP Export.
    by exists fd.
  have := linear_exportcallP h_x86_linearization_params lp_tmp_not_magic ok_lp p_call.
  case => fd [] ok_fd Export lp_call.
  exists (tunneling.tunnel_lfundef fn fd); split.
  - exact: get_fundef_tunnel_program ok_tp ok_fd.
  - exact: Export.
  move=> lm vm args' H H0 H1 H2 H3 H4 H5.
  have {lp_call} := lp_call lm vm args' H _ H1 H2 H3 _ H5.
  have [ -> [] -> _ ] := tunnel_program_invariants ok_tp.
  move => /(_ H0 H4)[] wt_args' [] vm' [] lm' [] res' [] lp_call M' ok_res' res_res' wt_res'.
  split; first exact: wt_args'.
  exists vm', lm', res'; split; cycle 1.
  - exact: M'.
  - exact: ok_res'.
  - exact: res_res'.
  - exact: wt_res'.
  clear -lp_call ok_tp.
  case: lp_call => fd ok_fd Export lp_exec ok_callee_saved.
  exists (tunneling.tunnel_lfundef fn fd).
  - exact: get_fundef_tunnel_program ok_tp ok_fd.
  - exact: Export.
  case: (lsem_run_tunnel_program ok_tp lp_exec).
  - by exists fd.
  - move => tp_exec _.
    rewrite /= size_tunnel_lcmd.
    exact: tp_exec.
  exact: ok_callee_saved.
Qed.

Lemma compiler_back_end_to_x86P
  entries
  (p : sprog)
  (xp : x86_prog)
  (rip : word Uptr)
  (m m' : mem)
  (fn: funname)
  args
  res :
  compiler_back_end_to_x86 cparams entries p = ok xp
  -> fn \in entries
  -> psem.sem_call p rip m fn args m' res
  -> exists xd : x86_fundef,
      [/\ get_fundef xp.(asm_funcs) fn = Some xd
        , xd.(asm_fd_export)
        & forall xm args',
            xm.(asm_rip) = rip
            -> asm_reg xm x86_decl.RSP = top_stack m
            -> match_mem m xm.(asm_mem)
            -> get_typed_reg_values xm xd.(asm_fd_arg) = ok args'
            -> List.Forall2 value_uincl args args'
  (* FIXME: well-typed? all2 check_ty_val fd.(asm_fd_tyin) args' ∧ *)
            -> exists xm' res',
                [/\ asmsem_exportcall x86_callee_saved xp fn xm xm'
                  , match_mem m' xm'.(asm_mem)
                  , get_typed_reg_values xm' xd.(asm_fd_res) = ok res'
                    & List.Forall2 value_uincl res res'
                ]
      ].
Proof.
  rewrite /compiler_back_end_to_x86; t_xrbindP => lp ok_lp ok_xp ok_fn p_call.
  have [fd [] ok_fd fd_export lp_call] := compiler_back_endP ok_lp ok_fn p_call.
  have [xd ->] := ok_get_fundef assemble_progP ok_xp ok_fd.
  have ok_lp_rsp := assemble_prog_RSP ok_xp.
  have [disj_rip ok_globs get_xfun] := assemble_progP ok_xp.
  case/assemble_fdI =>
    rsp_not_arg
    /allP ok_callee_saved
    [] xbody
    [] xargs
    [] xres
    [] ok_xbody ok_xargs ok_xres
    -> {xd}.
  eexists; split; first reflexivity.
  - by rewrite fd_export.
  move=> xm args' ok_rip ok_rsp M /= ok_args' ok_args.

  set s :=
    estate_of_asm_mem
      (asm_e := x86_extra.x86_extra)
      (top_stack m)
      (lp_rip lp)
      (lp_rsp lp)
      xm.
  have wf_s : wf_vm (evm s).
  - exact: wf_vmap_of_asm_mem.

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

  have := lp_call _ _ _ wf_s _ M _ ok_args.

  case.
  - have := XM (ARReg x86_decl.RSP).
    rewrite /= -ok_lp_rsp /get_var /=.
    case: _.[_]%vmap =>
      [ | [] // ] [] /= sz w sz_le_Uptr /ok_inj /Vword_inj[] ?;
      subst => /=.
    by rewrite pword_of_wordE ok_rsp => ->.
  - rewrite -ok_args'.
    apply: mapM_factorization ok_xargs.
    rewrite /typed_reg_of_vari /=.
    move => [x _] r /= h.
    by rewrite (asm_typed_reg_of_varI (asm_e := x86_extra.x86_extra) h).
  - case: LM => _ Y _ _ _ _.
    move: Y; rewrite /get_var /=.
    rewrite /mk_ptr /=.
    case: _.[_]%vmap =>
      /= [ | [] // ] [] /= sz w sz_le_Uptr /ok_inj /Vword_inj[] ?;
      subst => /=.
    by rewrite pword_of_wordE => ->.
  - move => /=.
    apply/andP; split.
    + by rewrite (XM (ARReg x86_decl.RAX)).
    apply/allP => x /ok_callee_saved.
    rewrite /is_arreg /=.
    case hx: asm_typed_reg_of_var => [ [ r | | ] | ] // _.
    by rewrite (asm_typed_reg_of_varI hx) XM.
    move=>
      _wt_largs
      [] vm'
      [] lm'
      [] res'
      [] {} lp_call M' ok_res' res_res' _wt_res'.

  have :=
    asm_gen_exportcall
      eval_assemble_cond
      assemble_extra_op
      assemble_progP
      ok_xp
      lp_call
      _
      LM.

  case.
  - apply/allP => _ /in_map[] r _ ->.
    by rewrite (XM (ARReg r)).

  move=> xm' xp_call LM'.

  have :
    exists2 res'', get_typed_reg_values xm' xres = ok res''
                   & List.Forall2 value_uincl res' res''.
  - move/mapM_Forall2: ok_res'.
    move/mapM_Forall2: ok_xres {res_res' _wt_res'} res'.
    case: LM' => /=_ _ _; clear => R X F.
    elim.
    + move=> _ /List_Forall2_inv_l ->. by exists [::].
    case => ? /= xi r xs rs.
    move=> /(asm_typed_reg_of_varI (asm_e := x86_extra.x86_extra)).
    move=> /= -> xs_rs ih.
    move=> ? /List_Forall2_inv_l[] v [] vs [] ?; subst.
    case => ok_v /ih [] vs' -> vs_vs'.
    suff : exists2 v', get_typed_reg_value xm' r = ok v' & value_uincl v v'.
    + case => v' /= -> v_v'; exists (v' :: vs'); first by [].
      by constructor.
    case: r ok_v => r.
    + by move=> /R /= h; eexists; first reflexivity.
    + by move=> /X /= h; eexists; first reflexivity.
    rewrite get_varE; t_xrbindP => /= b ok_b ?; subst v.
    have := F r b.
    rewrite /= ok_b => /(_ erefl).
    by case: (asm_flag xm' r) => // _ <-; exists b.
  case => res'' ok_res'' res'_res''.
  exists xm', res''; split; first exact: xp_call.
  - by case: LM' => /= <-.
  - exact: ok_res''.
  apply: Forall2_trans res_res' res'_res''.
  exact: value_uincl_trans.
Qed.

(* Agreement relation between source and target memories.
   Expressed in a way that streamlines the composition of compiler-correctness theorems (front-end and back-end).
  TODO: There might be an equivalent definition that is clearer.
*)
Record mem_agreement (m m': mem) (gd: pointer) (data: seq u8) : Prop :=
  { ma_ghost : mem
  ; ma_extend_mem : extend_mem m ma_ghost gd data
  ; ma_match_mem : match_mem ma_ghost m'
  ; ma_stack_stable : stack_stable m ma_ghost
  ; ma_stack_range : (wunsigned (stack_limit ma_ghost) <= wunsigned (top_stack m'))%Z
  }.

Lemma compile_prog_to_x86P
      entries
      subroutine
      (p : prog)
      (xp : x86_prog)
      (m m' : mem)
      (fn: funname)
      va
      vr
      xm :
  compile_prog_to_x86 cparams aparams entries subroutine p = ok xp
  -> fn \in entries
  -> sem.sem_call p m fn va m' vr
  -> mem_agreement m (asm_mem xm) (asm_rip xm) (asm_globs xp)
  -> enough_stack_space xp fn (top_stack m) (asm_mem xm)
  -> exists xd : x86_fundef,
      [/\
         get_fundef (asm_funcs xp) fn = Some xd
        , asm_fd_export xd
        & forall args',
            asm_reg xm x86_decl.RSP = top_stack m
            -> get_typed_reg_values xm (asm_fd_arg xd) = ok args'
            -> List.Forall2 value_uincl va args'
  (* FIXME: see comment in compiler_back_end_to_x86P *)
            -> exists xm' res',
                [/\ asmsem_exportcall x86_callee_saved xp fn xm xm'
                  , mem_agreement m' (asm_mem xm') (asm_rip xm') (asm_globs xp)
                  , get_typed_reg_values xm' (asm_fd_res xd) = ok res'
                  & List.Forall2 value_uincl vr res'
                ]
      ].
Proof.
  rewrite /compile_prog_to_x86; t_xrbindP => sp ok_sp ok_xp ok_fn p_call [] mi.
  have [rsp_eq ->] := compiler_back_end_to_x86_meta ok_xp.
  move=> mi1 mi2 mi3 mi4.
  rewrite (ss_top_stack mi3).
  move=> /(enough_stack_space_alloc_ok ok_xp ok_fn mi4) ok_mi.
  have := compiler_front_endP ok_sp ok_fn p_call mi1 ok_mi.
  case => vr' [] mi' [] vr_vr' sp_call m1.
  have := compiler_back_end_to_x86P ok_xp ok_fn sp_call.
  case => xd [] ok_xd export /(_ _ _ erefl _ mi2) xp_call.
  exists xd; split => //.
  move=> args' ok_RSP ok_args' va_args'.
  have := xp_call _ ok_RSP ok_args' va_args'.
  case => xm' [] res' [] {} xp_call m2 ok_res' vr'_res'.
  exists xm', res';
    split => //;
    last exact: Forall2_trans value_uincl_trans vr_vr' vr'_res'.
  case: xp_call => _ _ _ /= /asmsem_invariantP /= xm_xm' _.
  exists mi'.
  - rewrite -(asmsem_invariant_rip xm_xm').
    exact: m1.
  - exact: m2.
  - transitivity mi; last exact: sem_call_stack_stable_sprog sp_call.
    transitivity m; last exact: mi3.
    symmetry; exact: sem_call_stack_stable p_call.
  rewrite
    -(ss_limit (sem_call_stack_stable_sprog sp_call))
    -(ss_top_stack (asmsem_invariant_stack_stable xm_xm')).
  exact: mi4.
Qed.

(*
Let Kj : ∀ rip glob m vr (P Q: _ → _ → Prop),
        (∀ m' vr', P m' vr' → Q m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ P m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ Q m' vr')
    := λ rip glob m vr P Q h x,
      let 'ex_intro m' (ex_intro vr' (conj u (conj v p))) := x in
      ex_intro _ m' (ex_intro _ vr' (conj u (conj v (h m' vr' p)))).

Let Km : ∀ rip glob m vr (P: _ → Prop) (Q: _ → _ → Prop),
        (∀ vr, P vr → ∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ Q m' vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ extend_mem m m' rip glob ∧ Q m' vr')
  := λ rip glob m vr P Q h x,
      let 'ex_intro vr' (conj u p) := x in
      let 'ex_intro m' (ex_intro vr'' (conj u' q)) := h vr' p in
      ex_intro _ m' (ex_intro _ vr'' (conj (Forall2_trans value_uincl_trans u u') q)).
*)

(*
Lemma compile_progP entries (p: prog) (lp: lprog) mem fn va mem' vr:
  compile_prog cparams entries p = cfok lp ->
  fn \in entries ->
  sem.sem_call p mem fn va mem' vr ->
  forall meml rip, 
    extend_mem mem meml rip lp.(lp_globs) ->
    (forall f, get_fundef lp.(lp_funcs) fn = Some f -> 
       exists p, alloc_stack meml (lfd_stk_size f) = ok p) ->
  ∃ meml' vr',
    List.Forall2 value_uincl vr vr' ∧
    extend_mem mem' meml' rip lp.(lp_globs) /\
    lsem_fd lp rip meml fn va meml' vr'.
Proof.
  rewrite /compile_prog.
  apply: rbindP=> p0 Hp0. rewrite !print_uprogP.
  apply: rbindP=> pca Hpca. rewrite !print_uprogP.
  apply: rbindP=> p1 Hp1. rewrite !print_uprogP.
  apply: rbindP => -[] Hv.
  apply: rbindP=> pv Hpv. rewrite !print_uprogP.
  apply: rbindP=> -[] Hps.
  apply: rbindP=> ps' Hps'. rewrite !print_uprogP.
  apply: rbindP=> -[] He.
  apply: rbindP => pg Hpg. rewrite !print_uprogP.
  apply: rbindP => _ /assertP Hlower.
  apply: rbindP => pstk Hpstk. rewrite !print_sprogP.
  apply: rbindP=> -[] He'.
  apply: rbindP=> pd Hpd. rewrite !print_sprogP.
  apply: rbindP=> pl Hpl [] <-. rewrite !print_linearP.
  move=> Hin Hcall meml rip Hex Halloc.
 (* have Haok : alloc_ok pstk fn meml.
  + rewrite /alloc_ok=> fd Hfd.
    move: Hpl; rewrite /linear_prog; t_xrbindP => ?? lfuncs Hpl [] ?; subst pl.
    move: (get_map_cfprog_gen Hpl Hfd)=> [f' [Hf'1 Hf'2]].
    apply: rbindP Hf'1=> [fn' Hfn'] [] Hf'.
    have := Halloc _ Hf'2.
    by rewrite -Hf' /=. *)
  have va_refl := List_Forall2_refl va value_uincl_refl.
  have eqg : lp_globs pl = sp_globs pd.(p_extra).
  + by move: Hpl; rewrite /linear_prog; t_xrbindP => ???? <-. 
  move: Hex; rewrite eqg => Hex.
  apply: Kj; first by exact: (linear_fdP Hpl).
  apply: Km. 
  + by move=> vr' Hvr'; apply: (stack_alloc_proof.alloc_progP (ev:= tt) Hpstk _ Hex Haok); exact: Hvr'.
  apply: Ki; first by move => vr'; apply: (dead_code_callPu Hpd).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocRegU.alloc_callP He'); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (lower_callP _ _ _ Hlower).
  apply: Ki; first by move => vr';apply: (RGP.remove_globP Hpg).
  apply: K'; first by move => vr' Hvr'; apply: (CheckExpansion.alloc_callP He); exact: Hvr'.
  rewrite surj_prog.
  apply: K'; first by move => vr' Hvr'; apply: (remove_init_fdPu va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_code_callPu Hps').
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocRegU.alloc_callP Hps); exact: Hvr'.
  rewrite surj_prog. 
  apply: Ki; first by move => vr'; exact: (dead_code_callPu Hpv).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocRegU.alloc_callP Hv); exact: Hvr'.
  rewrite surj_prog.
  apply: K'; first by move => vr' Hvr'; apply: (const_prop_callP _ va_refl); exact: Hvr'.
  apply: K'; first by move => vr' Hvr'; apply: (unrollP Hp1 _ va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_calls_err_seqP (sCP:= sCP_unit) Hpca).
  apply: K'; first by move => vr' Hvr'; apply: (inline_call_errP Hp0 va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: psem_call.
  exists vr; split => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
Qed.

Lemma compile_prog_to_x86P entries (p: prog) (xp: xprog) m1 fn va m2 vr :
  compile_prog_to_x86 cparams entries p = cfok xp →
  fn \in entries →
  sem.sem_call p m1 fn va m2 vr →
  forall m1' wrip, 
  extend_mem m1 m1' wrip xp.(xp_globs) ->
  (∀ f, get_fundef xp.(xp_funcs) fn = Some f →
     ∃ p, alloc_stack m1' (xfd_stk_size f) = ok p) →
  ∃ fd va',
    get_fundef (p_funcs p) fn = Some fd ∧
    mapM2 ErrType truncate_val (f_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef xp.(xp_funcs) fn = Some fd' ∧
  ∀ st1,
    List.Forall2 value_uincl va' (get_arg_values st1 fd'.(xfd_arg)) →
    st1.(xmem) = m1' →
  ∃ st2,
    x86sem_fd xp wrip fn st1 st2 ∧
    List.Forall2 value_uincl vr (get_arg_values st2 fd'.(xfd_res)) ∧
    extend_mem m2 st2.(xmem) wrip xp.(xp_globs).
Proof.
apply: rbindP=> lp hlp; t_xrbindP => /= _ /assertP /allP ok_sig hxp hfn hsem m1' rip Hex hsafe.
have heq: xp_globs xp = lp_globs lp.
+ by move: hxp; rewrite /assemble_prog; t_xrbindP => _ _; case: x86_variables.reg_of_string => //; t_xrbindP => _ ? _ <-.
rewrite heq in Hex.
have hlsem := compile_progP hlp hfn hsem Hex.
case: hlsem.
- move => fd hfd.
  move: hxp; rewrite /assemble_prog; t_xrbindP => _ _; case: x86_variables.reg_of_string => // sp; t_xrbindP => fs hfs ?; subst xp.
  have [xfd hxfd] := get_map_cfprog_gen hfs hfd.
  by move => /hsafe; rewrite (assemble_fd_stk_size hxfd).
move/ok_sig: hfn.
case: hsem => {m1 m2 hsafe fn va vr Hex} m1 m2 fn fd va va' st1 vm2 vr vr1 ok_fd ok_va _ _ _ _ hsig m2' [vr'] [ok_vr'] [hm2' hlsem].
exists fd, va.
split; first exact: ok_fd.
split; first exact: ok_va.
case: (assemble_fdP hxp hlsem) => fd' [va1] [ok_fd'] [ok_va1] [xd] [ok_xd h].
move: ok_va1.
have -> : lfd_tyin fd' = f_tyin fd.
- by move: hsig; rewrite /check_signature ok_fd' ok_fd => /eqP [].
rewrite ok_va => - [?]; subst va1.
exists xd; split; first exact: ok_xd.
move => st hva hm1.
have [st2 [hxsem [hvr' hm2]]] := h st hva hm1.
exists st2.
split; first exact: hxsem.
split; first exact: (Forall2_trans value_uincl_trans ok_vr' hvr').
by rewrite heq hm2.
Qed.
*)

End PROOF.
