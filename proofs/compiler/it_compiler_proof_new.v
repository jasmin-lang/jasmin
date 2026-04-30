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
  it_linearization_proof
  it_merge_varmaps_proof
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
Require Import linearization_composition.


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

(* ============================================================ *
 * PLAN — Filling the admits in [it_compiler_back_endP]
 *
 *   Two admits remain:
 *     (a) line ~250 — [admit] for the RAns conversion inside
 *         [xrutt_weaken_v1] applied to
 *         [mix_ilsem_exportcall_ilsem_exportcall];
 *     (b) line ~255 — the closing [Admitted.], standing in for
 *         six unresolved goals: 3 [hpost] obligations of the three
 *         [wkequiv_io_trans] calls, 2 [hpre] obligations (steps 1
 *         and 2; step 3's [hpre] is already discharged by
 *         [exists i1] near line 253), and the [hRR] obligation of
 *         [xrutt_weaken_v1].
 *
 *   The previous proof in [it_compiler_proof.v] used the admitted
 *   monolithic [it_linear_exportcallP] (in [linearization_composition.v],
 *   lines 71-127). We replace it here with the explicit chain
 *   [w_ovm] -> [w_lin] -> mix-to-ilsem bridge -> [w_sz], stitched by
 *   three [wkequiv_io_trans] applications. Each trans application
 *   MUST receive an explicit [P23] (and where needed [P12]/[Q12]/[Q23])
 *   so unification does not pick a metavar that later blocks the side
 *   conditions.
 *
 * ------------------------------------------------------------ *
 * 1. Four-piece chain and the itrees involved
 * ------------------------------------------------------------ *
 *
 *   isem_stack sp rip fn                         (input: fstate)
 *   = isem_fun (sp) rip fn  (with sCP_stack, direct_c, withsubword)
 *
 *     |  ↑1 = w_ovm = merge_varmaps_export_call_checkP hexp
 *     v
 *   isem_exportcall_check var_tmps sp rip fn    (input: estate)
 *
 *     |  ↑2 = w_lin = linear_exportcallP haparams ok_lp
 *     |       (provided by [it_linearization_proof.v] line 4984)
 *     v
 *   mix_ilsem_exportcall lp fn                   (input: estate)
 *
 *     |  ↑3 = mix-to-ilsem bridge, via:
 *     |       xrutt_weaken_v1 ... ; exact: mix_ilsem_exportcall_ilsem_exportcall
 *     |       (lemma at [proofs/lang/linear_sem.v:720])
 *     v
 *   ilsem_exportcall lp fn                       (input: estate)
 *
 *     |  ↑4 = w_sz = istack_zeroization_lprogP_new haparams _ ok_zp get_lfd_lp
 *     |       ([stack_zeroization_proof.v:690])
 *     v
 *   ilsem_exportcall zp fn                       (input: estate)
 *
 *   The final tunneling step (zp -> tp) was already absorbed by
 *   [wkequiv_io_eutt_r (tunnel_funcs ok_tp fn)]; the goal after
 *   that rewrite has [ilsem_exportcall zp fn] as its RHS.
 *
 * ------------------------------------------------------------ *
 * 2. Predicate vocabulary (referenced by name; brief summary)
 * ------------------------------------------------------------ *
 *
 *   [back_end_pre lfd s t]      — this file, lines ~133-146.
 *      Source [s : fstate], target [t : estate]. Conjuncts:
 *        evm t .[vid lp_rsp tp] = Vword (top_stack (fmem s));
 *        evm t .[vid lp_rip tp] = Vword rip;
 *        values_uincl (fvals s) (lget_args lfd (evm t));
 *        match_mem (fmem s) (emem t);
 *        fscs s = escs t;
 *        vm_initialized_on (evm t) (lfd_callee_saved lfd);
 *        allocatable_stack (fmem s) (lfd_total_stack lfd).
 *      Note: [lfd] here is [tunnel_lfundef fn zfd]; via
 *      [tunnel_program_invariants ok_tp] and
 *      [stack_zeroization_lprog_invariants ok_zp] the relevant
 *      [lp_rsp]/[lp_rip] and [lfd_callee_saved] are preserved
 *      across tunneling and zeroization (already extracted above
 *      as [rip_eq]/[rsp_eq]/[globs_eq] and [rip_eq']/[rsp_eq']
 *      and [inv_cs]/[inv_arg]/[inv_res]/...).
 *
 *   [back_end_post fn lfd s t s' t']  — this file, lines ~148-160.
 *      Conjuncts:
 *        values_uincl (fvals s') (lget_res lfd (evm t'));
 *        match_mem (fmem s') (emem t');
 *        fscs s' = escs t';
 *        zeroized_s fn (fmem s) (emem t) (emem t').
 *
 *   [preF_ovm fs t]   — pre of [merge_varmaps_export_call_checkP],
 *      [it_merge_varmaps_proof.v:1276-1291]. Conjuncts:
 *        fscs fs = escs t;
 *        fmem fs = emem t;
 *        case [get_fundef p.(p_funcs) fn] = Some fd:
 *          ∃ args', evm t .[vid sp_rsp] = Vword (top_stack (fmem fs)),
 *                   evm t .[vid sp_rip] = Vword global_data,
 *                   get_var_is false (evm t) (f_params fd) = ok args',
 *                   List.Forall2 value_uincl (fvals fs) args'.
 *      Beware: target uses [vid sp_rsp]/[vid sp_rip] (the SOURCE
 *      sprog rsp/rip names); after [ok_lp] these equal [vid lp_rsp lp]
 *      and [vid lp_rip lp] up to [meta_rsp] / [linear_prog_rip] (extract
 *      via [compiler_back_end_meta print_linearP ok_lp] or directly
 *      from [ok_lp]'s shape, as in [it_compiler_proof.v:1111]).
 *
 *   [postF_ovm fs t fs' t']  — post of [merge_varmaps_export_call_checkP],
 *      same file, lines ~1295-1306. Conjuncts:
 *        fscs fs' = escs t';
 *        fmem fs' = emem t';
 *        case [get_fundef ... fn] = Some fd:
 *          ∃ res', get_var_is false (evm t') (f_res fd) = ok res',
 *                  List.Forall2 value_uincl (fvals fs') res'.
 *      Note the input-independent shape ([wkequiv], not [wkequiv_io]);
 *      [wkequiv = wkequiv_io] with [Q] not depending on inputs
 *      ([relational_logic.v:222-231]).
 *
 *   [preF_export gd fn s ls]  — [it_linearization_proof.v:4942-4957],
 *      with [p := sp], [p' := lp]. Conjuncts (after the [get_fundef]
 *      match takes the Some/Some branch):
 *        evm ls .[vid lp_rsp lp] = Vword (top_stack (emem s));
 *        evm ls .[vid lp_rip lp] = Vword gd;
 *        vm_initialized_on (evm ls) (lfd_callee_saved lfd_lp);
 *        (sf_stk_max + wsize_size sf_align - 1 <= wunsigned (top_stack (emem s)))%Z;
 *        evm s <=1 evm ls;
 *        escs s = escs ls;
 *        match_mem (emem s) (emem ls).
 *
 *   [postF_export fn s ls s' ls']  — same file, lines ~4959-4977. Conjuncts:
 *        evm ls' .[vid lp_rsp lp] = Vword (top_stack (emem s));
 *        match_mem (emem s') (emem ls');
 *        target_mem_unchanged (emem s) (align_top_stack ...)
 *                             (sf_stk_max ...) (emem ls) (emem ls');
 *        escs s' = escs ls';
 *        stack_stable (emem s) (emem s');
 *        ∀ res, get_var_is false (evm s') (f_res fd) = ok res ->
 *               ∃ res', get_var_is false (evm ls') (lfd_res lfd_lp) = ok res' /\
 *                       List.Forall2 value_uincl res res'.
 *
 *   [sz_pre lp lfd s1 s2]   — [stack_zeroization_proof.v:672-679].
 *      [∃ ptr, evm s1 .[vid lp_rsp lp] = Vword ptr  /\
 *              s1 = s2  /\
 *              (lfd_stk_max + wsize_size lfd_align - 1 <= wunsigned ptr)%Z /\
 *              valid_between (emem s1)
 *                (align_word lfd_align ptr - wrepr _ lfd_stk_max)
 *                (lfd_stk_max lfd) ].
 *
 *   [sz_pos lp fn lfd s1 s2 s1' s2']  — same file, lines ~681-688.
 *      [∃ ptr, evm s1 .[vid lp_rsp lp] = Vword ptr /\
 *              escs s1' = escs s2' /\
 *              (evm s1') =[sv_of_list v_var (lfd_res lfd)] (evm s2') /\
 *              match_mem_zero_export (emem s1') (emem s2')
 *                (align_word lfd_align ptr - wrepr _ lfd_stk_max)
 *                (lfd_stk_max lfd) (szs_of_fn fn) ].
 *
 *   [eq] (Coq's syntactic equality) — used for the mix-to-ilsem step,
 *      both as P12 and as Q12 (the bridge changes only the event
 *      contract, never the estate).
 *
 * ------------------------------------------------------------ *
 * 3. Three [wkequiv_io_trans] applications: explicit P/Q
 * ------------------------------------------------------------ *
 *
 *   ALWAYS pass P23 (and where applicable Q12/Q23) explicitly to
 *   [wkequiv_io_trans]. Without explicit predicates, the side-condition
 *   metavariables become unprovable. The signature is
 *   ([relational_logic.v:2747]):
 *
 *     wkequiv_io_trans
 *       (P12 : rel I1 I2) (P23 : rel I2 I3) (P13 : rel I1 I3)
 *       (Q12 : rel_io I1 I2 O1 O2) (Q23 : rel_io I2 I3 O2 O3)
 *       (Q13 : rel_io I1 I3 O1 O3) F1 F2 F3 :
 *       (∀ i1 i3, P13 i1 i3 -> ∃2 i2, P12 i1 i2 & P23 i2 i3) ->
 *       (∀ i1 i2 i3 o1 o3, P12 i1 i2 -> P23 i2 i3 ->
 *          rcompose (Q12 i1 i2) (Q23 i2 i3) o1 o3 -> Q13 i1 i3 o1 o3) ->
 *       wkequiv_io P12 F1 F2 Q12 ->
 *       wkequiv_io P23 F2 F3 Q23 ->
 *       wkequiv_io P13 F1 F3 Q13.
 *
 *   --- Split A (outer): isem_stack ===> isem_exportcall_check ===> ilsem_exportcall zp ---
 *     P13 := back_end_pre lfd
 *     Q13 := back_end_post fn lfd
 *     P12 := preF_ovm                         (from w_ovm)
 *     Q12 := postF_ovm                        (from w_ovm)
 *     P23 := fun (i2 i3 : estate) =>
 *              preF_export rip fn i2 i3 /\ sz_pre lp lfd_lp i3 i3
 *     Q23 := fun (i2 i3 : estate) (o2 o3 : estate) =>
 *              exists o3', postF_export fn i2 i3 o2 o3'
 *                       /\ sz_pos lp fn lfd_lp i3 i3 o3' o3
 *     w12 := w_ovm
 *     w23 := (the result of Splits B+C below)
 *
 *   --- Split B (middle): isem_exportcall_check ===> mix_ilsem_exportcall lp ===> ilsem_exportcall zp ---
 *     P13 := the P23 from Split A
 *     Q13 := the Q23 from Split A
 *     P12 := preF_export rip fn               (from w_lin)
 *     Q12 := postF_export fn                  (from w_lin)
 *     P23 := sz_pre lp lfd_lp
 *     Q23 := sz_pos lp fn lfd_lp
 *     w12 := w_lin
 *     w23 := (the result of Split C below)
 *
 *   --- Split C (inner): mix_ilsem_exportcall lp ===> ilsem_exportcall lp ===> ilsem_exportcall zp ---
 *     P13 := sz_pre lp lfd_lp                (= Split B's P23)
 *     Q13 := sz_pos lp fn lfd_lp             (= Split B's Q23)
 *     P12 := eq          (mix and ilsem operate on the same estate)
 *     Q12 := fun (_ _ : estate) (o1 o2 : estate) => o1 = o2
 *            (i.e. the input-independent equality)
 *     P23 := sz_pre lp lfd_lp
 *     Q23 := sz_pos lp fn lfd_lp
 *     w12 := the mix-to-ilsem bridge (Section 5 below)
 *     w23 := w_sz   (= [istack_zeroization_lprogP_new ... _ ok_zp get_lfd_lp];
 *                   the [_] is [Sv.In (vid (lp_rsp lp)) callee_saved],
 *                   discharged via [lp_rspE ok_lp] and [rsp_in_callee_saved],
 *                   already on line ~252).
 *
 * ------------------------------------------------------------ *
 * 4. The six side conditions (organized by Split)
 * ------------------------------------------------------------ *
 *
 *   ----- Split A hpre -----
 *   Goal:
 *     forall i1 i3, back_end_pre lfd i1 i3 ->
 *       exists2 i2 : estate,
 *           preF_ovm i1 i2
 *         & preF_export rip fn i2 i3 /\ sz_pre lp lfd_lp i3 i3.
 *
 *   Construction. Set
 *     i2 := {| escs := fscs i1; emem := fmem i1; evm := evm i3 |}.
 *   This is forced because [preF_ovm] requires [fmem i1 = emem i2],
 *   while [back_end_pre] only gives [match_mem (fmem i1) (emem i3)].
 *   Reuse [evm i3] so that all the vmap conjuncts in [preF_ovm] and
 *   [preF_export] are inherited from [back_end_pre]'s
 *   [vmt.[vid lp_rsp tp]/lp_rip tp]/callee_saved/values_uincl] data,
 *   modulo the tunneling/zeroization invariants.
 *
 *   preF_ovm i1 i2:
 *     (1) fscs i1 = escs i2: by definition.
 *     (2) fmem i1 = emem i2: by definition.
 *     (3) get_fundef sp.(p_funcs) fn = Some fd: provided by [hexp]
 *         ([is_export sp fn]) — already in scope as [hexp] above.
 *     (4) ∃ args', vmap conjuncts:
 *         · evm i2 .[vid sp_rsp] = Vword (top_stack (fmem i1)):
 *           rewrite [vid sp_rsp] back to [vid lp_rsp lp] using
 *           [meta_rsp] (= [proj1 (compiler_back_end_meta print_linearP ok_lp)]),
 *           then chase [lp_rsp lp = lp_rsp tp] backwards via
 *           [stack_zeroization_lprog_invariants ok_zp]
 *           ([rsp_eq']) and [tunnel_program_invariants ok_tp]
 *           ([rsp_eq]). The original hypothesis is in [back_end_pre lfd]'s
 *           first conjunct: evm i3 .[vid lp_rsp tp] = Vword (top_stack ms).
 *         · evm i2 .[vid sp_rip] = Vword rip = Vword global_data: same
 *           shape with [linear_prog_rip] / [rip_eq] / [rip_eq'].
 *         · get_var_is false (evm i2) (f_params fd) = ok args': use the
 *           linearization invariant connecting [lfd_arg lfd] to
 *           [f_params fd] (extract via [linearization_proof.checked_prog
 *           ok_lp get_sfd] together with [inv_arg], analogously to
 *           [it_compiler_proof.v:763]). Choose
 *           args' := [seq (evm i2).[v_var x] | x <- f_params fd]
 *           and use [get_var_is_get_var] / [get_var_uincl] to package.
 *         · List.Forall2 value_uincl (fvals i1) args': from
 *           [back_end_pre]'s [values_uincl args (lget_args lfd vmt)] and
 *           the args/params correspondence above.
 *
 *   preF_export rip fn i2 i3:
 *     · evm i3 .[vid lp_rsp lp] = Vword (top_stack (emem i2)):
 *       [emem i2 = fmem i1], and [back_end_pre] gives the analogue
 *       at [vid lp_rsp tp]; bridge with [rsp_eq']/[rsp_eq].
 *     · evm i3 .[vid lp_rip lp] = Vword rip: similarly.
 *     · vm_initialized_on (evm i3) (lfd_callee_saved lfd_lp):
 *       [back_end_pre]'s callee_saved hypothesis is on
 *       [lfd_callee_saved (tunnel_lfundef fn zfd)]; rewrite via
 *       [inv_cs] and the trivial fact that tunneling does not change
 *       [lfd_callee_saved] (already in scope as [tunnel_program]
 *       invariants).
 *     · (sf_stk_max fd + wsize_size sf_align - 1 ≤ wunsigned (top_stack (fmem i1)))%Z:
 *       derive from [allocatable_stack (fmem i1) (lfd_total_stack lfd)]
 *       in [back_end_pre], unfolding [allocatable_stack] and
 *       [lfd_total_stack] across [tunnel_lfundef] and the stack-zero
 *       invariants ([inv_stkmax], [inv_align]). This is the same
 *       computation as [it_compiler_proof.v:743-758].
 *     · evm i2 <=1 evm i3: by definition (evm i2 = evm i3) and reflexivity.
 *     · escs i2 = escs i3: i2's escs is fscs i1; i3's escs equals fscs i1
 *       by [back_end_pre]'s [s.(fscs) = t.(escs)].
 *     · match_mem (emem i2) (emem i3): [emem i2 = fmem i1], so this is
 *       exactly [back_end_pre]'s [match_mem (fmem i1) (emem i3)].
 *
 *   sz_pre lp lfd_lp i3 i3:
 *     Witness ptr := top_stack (fmem i1) (= top_stack (emem i2)).
 *     · evm i3 .[vid lp_rsp lp] = Vword ptr: bridge as above.
 *     · i3 = i3: refl.
 *     · (lfd_stk_max lfd_lp + wsize_size lfd_align - 1 ≤ wunsigned ptr)%Z:
 *       same allocatable derivation as for [preF_export].
 *     · valid_between (emem i3) (align_word lfd_align ptr - wrepr _ lfd_stk_max)
 *                     (lfd_stk_max lfd_lp):
 *       this is the bottleneck. Mirror [it_compiler_proof.v:769-826]:
 *       extract [hmem.(valid_stk)] from the [match_mem (fmem i1) (emem i3)]
 *       conjunct of [back_end_pre], then prove the [zbetween] / [pointer_range]
 *       chain that the bottom region is below the top stack and within
 *       the source's stack frame.
 *
 *   ----- Split A hpost -----
 *   Goal:
 *     forall i1 i2 i3 o1 o3,
 *       preF_ovm i1 i2 ->
 *       (preF_export rip fn i2 i3 /\ sz_pre lp lfd_lp i3 i3) ->
 *       rcompose (postF_ovm i1 i2)
 *                (fun (o2 o3 : estate) =>
 *                   exists o3', postF_export fn i2 i3 o2 o3'
 *                            /\ sz_pos lp fn lfd_lp i3 i3 o3' o3)
 *                o1 o3 ->
 *       back_end_post fn lfd i1 i3 o1 o3.
 *
 *   That is: from [postF_ovm i1 i2 o1 o2], [postF_export fn i2 i3 o2 o3'],
 *   and [sz_pos lp fn lfd_lp i3 i3 o3' o3] (for some o2, o3'), derive the
 *   four conjuncts of [back_end_post fn lfd i1 i3 o1 o3]:
 *     · values_uincl (fvals o1) (lget_res lfd (evm o3)):
 *       chain [postF_ovm]'s [List.Forall2 value_uincl (fvals o1) res']
 *       (with [res' = get_var_is (f_res fd) (evm o2)]) into
 *       [postF_export]'s lfd_res-level translation, then use [sz_pos]'s
 *       [(evm o3') =[sv_of_list v_var (lfd_res lfd_lp)] (evm o3)] to push
 *       the [evm o3'] read to [evm o3]. Bridge [lfd_res lfd] to
 *       [lfd_res lfd_lp] by [inv_res]. Mirrors [it_compiler_proof.v:891-898].
 *     · match_mem (fmem o1) (emem o3):
 *       [postF_ovm] gives [fmem o1 = emem o2]; [postF_export] gives
 *       [match_mem (emem o2) (emem o3')]; [sz_pos]'s
 *       [match_mem_zero_export (emem o3') (emem o3) bottom max szs_of_fn]
 *       gives, on points outside the bottom region, equal reads, and on
 *       points inside, [read = ok 0%R]. Combine using
 *       [match_mem_read_incl_mem] and the disjointness of source-stack
 *       points from the bottom region, exactly as in
 *       [it_compiler_proof.v:899-923].
 *     · fscs o1 = escs o3:
 *       [postF_ovm] gives [fscs o1 = escs o2]; [postF_export] gives
 *       [escs o2 = escs o3']; [sz_pos] gives [escs o3' = escs o3]. Chain.
 *     · zeroized_s fn (fmem i1) (emem i3) (emem o3):
 *       unfold [zeroized_s]; assume [stack_zero_info fn <> None] and
 *       fix [pr]; case-split on whether [pr] lies in the bottom region
 *       and use [sz_pos]'s [match_mem_zero_export] (its [read_zero] /
 *       [read_untouched] / [valid_eq] fields). Mirror
 *       [it_compiler_proof.v:926-994].
 *
 *   ----- Split B hpre -----
 *   Goal:
 *     forall i2 i3,
 *       preF_export rip fn i2 i3 /\ sz_pre lp lfd_lp i3 i3 ->
 *       exists2 i2', preF_export rip fn i2 i2' & sz_pre lp lfd_lp i2' i3.
 *
 *   Choose i2' := i3. Both conjuncts of the input directly furnish the
 *   two halves; close with [by move=> ?? [??]; exists i3] (modulo
 *   [exists2] mechanics).
 *
 *   ----- Split B hpost -----
 *   Goal:
 *     forall i2 i2' i3 o2 o3,
 *       preF_export rip fn i2 i2' ->
 *       sz_pre lp lfd_lp i2' i3 ->
 *       rcompose (postF_export fn i2 i2') (sz_pos lp fn lfd_lp i2' i3) o2 o3 ->
 *       (exists o3', postF_export fn i2 i3 o2 o3'
 *                 /\ sz_pos lp fn lfd_lp i3 i3 o3' o3).
 *
 *   Since [sz_pre lp lfd_lp i2' i3] forces [i2' = i3] (its second
 *   conjunct), the goal collapses to the [rcompose] hypothesis.
 *   Destruct the [rcompose] to obtain [o2'] with [postF_export ... o2 o2']
 *   and [sz_pos ... o2' o3], then take o3' := o2'.
 *
 *   ----- Split C hpre  (already discharged in current code, line ~253) -----
 *   Goal:
 *     forall i1 i3, sz_pre lp lfd_lp i1 i3 ->
 *       exists2 i2, eq i1 i2 & sz_pre lp lfd_lp i2 i3.
 *   Closed by:  by move=> i1 i3 ?; exists i1.
 *
 *   ----- Split C hpost -----
 *   Goal:
 *     forall i1 i2 i3 o1 o3,
 *       i1 = i2 ->
 *       sz_pre lp lfd_lp i2 i3 ->
 *       rcompose (fun o1 o2 => o1 = o2) (sz_pos lp fn lfd_lp i2 i3) o1 o3 ->
 *       sz_pos lp fn lfd_lp i1 i3 o1 o3.
 *
 *   Destruct the [rcompose] to get o2 with [o1 = o2] and
 *   [sz_pos ... o2 o3]; subst [o2] for [o1] and [i1] for [i2]. The result
 *   is exactly [sz_pos ... i1 i3 o1 o3]. Note [sz_pos]'s state-input
 *   parameters are independent of the trans's [eq] so the input
 *   substitution is harmless — but DOUBLE-CHECK that [sz_pre lp lfd_lp]
 *   forces [i2 = i3] (it does), which makes the [i2/i3] occurrences in
 *   [sz_pos] interchangeable with the [i1/i3] in the goal.
 *
 * ------------------------------------------------------------ *
 * 5. The mix-to-ilsem bridge (line ~239-250)
 * ------------------------------------------------------------ *
 *
 *   The existing code does:
 *
 *     move=> s _ <-.    (* enters Split C's hw12, with P12 := eq, *)
 *                       (* introducing s, the unused i2, and the equation *)
 *     apply: (xrutt_weaken_v1
 *       (EE1 := errcutoff (is_error wE)) (EE2 := nocutoff)
 *       (EE1' := errcutoff (is_error wE)) (EE2' := nocutoff)); cycle 5.
 *     exact: mix_ilsem_exportcall_ilsem_exportcall.
 *
 *   This invokes [xrutt_weaken_v1] ([proofs/itrees/xrutt_facts.v:684])
 *   to coerce
 *     xrutt errcutoff nocutoff RPre_eq RPost_eq eq (mix...) (ilsem...)
 *   into
 *     xrutt errcutoff nocutoff EPreRel EPostRel (Q12_C s s) (mix...) (ilsem...).
 *
 *   With Q12_C := fun _ _ o1 o2 => o1 = o2 (chosen above), [Q12_C s s = eq]
 *   so [hRR] becomes [forall r1 r2, r1 = r2 -> r1 = r2] — closed by [done].
 *
 *   Five [xrutt_weaken_v1] side conditions remain after [cycle 5]:
 *     - hEE1: forall A e, IsCut_ errcutoff e -> IsCut_ errcutoff e   — done.
 *     - hEE2: forall A e, IsCut_ nocutoff   e -> IsCut_ nocutoff   e — done.
 *     - hREv: RPre_eq -> EPreRel.   Already closed by:
 *         move=> T1 T2 [e1|e1] [e2|e2] => //= -[?]; subst T1 => //= -[->].
 *         by move: e1 => [scs1 n1].
 *       Reasoning: [E0 = RndEvent syscall_state] has only one constructor
 *       [Rnd : syscall_state -> Z -> RndEvent (syscall_state * seq u8)].
 *       From [RPre_eq] (∃ h : T1 = T2, e2 = eq_rect _ E e1 _ h), since
 *       both T1, T2 must be [syscall_state * seq u8], the equation
 *       collapses (UIP on [Type] is not needed; [eq_rect] on [erefl]
 *       gives [e2 = e1]), and the [Rnd]/[Rnd] match yields
 *       [scs1 = scs2 /\ n1 = n2] (the body of [RndPre]).
 *
 *     - hRAns: EPostRel -> RPost_eq.   THIS IS THE [admit] AT LINE ~250.
 *       Goal (after [move=> T1 T2 [[e1]|[scs1 n1]] // [scs1' a1]
 *                      [[e2]|[scs2 n2]] // [scs2' a2]
 *                      [<- <-] a]):
 *         RPost_eq (Rnd scs1 n1) (scs1', a1) (Rnd scs1 n1) (scs2', a2) ...
 *           a being the post-relation hypothesis ((scs1', a1) = (scs2', a2))
 *
 *       [RPost_eq] unfolds to:
 *         forall (h : (syscall_state * seq u8) = (syscall_state * seq u8)),
 *           (scs2', a2) = eq_rect _ id (scs1', a1) _ h.
 *
 *       Use UIP on [Type] (or, more cleanly, [eq_rect_eq_dec] /
 *       [Eqdep_dec.UIP_refl_unit] / [Eqdep.EqdepTheory.UIP_refl] from
 *       [Coq.Logic.Eqdep] when type-decidability is unavailable). The
 *       cleanest tactic:
 *
 *         move=> h.
 *         rewrite (Eqdep.EqdepTheory.UIP_refl _ _ h) /=.
 *         exact: a.
 *
 *       (The hypothesis [a : (scs1', a1) = (scs2', a2)] is named 'a' by
 *       the existing [move=> ... a].) If using [Eqdep.EqdepTheory] is
 *       discouraged, an alternative is to show that [h] is [erefl] by
 *       pattern matching, but UIP_refl is direct. Importing
 *       [Eqdep.EqdepTheory] (transitive via [ITree.Basics.Basics] in
 *       most files) is already in scope.
 *
 *     - hRR: forall r1 r2, eq r1 r2 -> Q12_C s s r1 r2.   With
 *       [Q12_C s s = eq], this is [forall r1 r2, r1 = r2 -> r1 = r2] —
 *       discharged by [done]. (Note: this goal is currently part of the
 *       residual [Admitted.] at line ~255; once [Q12_C] is fixed
 *       explicitly to [fun _ _ o1 o2 => o1 = o2] in Split C above, the
 *       proof is one tactic.)
 *
 * ------------------------------------------------------------ *
 * 6. Integration — concrete recipe for editing the proof
 * ------------------------------------------------------------ *
 *
 *   Step 1. Replace the three [wkequiv_io_trans] applications with
 *           explicit [P12]/[P23]/[Q12]/[Q23] specifications, e.g.:
 *
 *     apply: (wkequiv_io_trans
 *       (P12 := preF_ovm)
 *       (P23 := fun (i2 i3 : estate) =>
 *                 preF_export rip fn i2 i3 /\ sz_pre lp lfd_lp i3 i3)
 *       (Q12 := postF_ovm)
 *       (Q23 := fun (i2 i3 : estate) (o2 o3 : estate) =>
 *                 exists o3', postF_export fn i2 i3 o2 o3'
 *                          /\ sz_pos lp fn lfd_lp i3 i3 o3' o3)
 *       _ _ w_ovm).
 *
 *   etc., similarly for Splits B and C, including
 *     (Q12 := fun (_ _ : estate) (o1 o2 : estate) => o1 = o2)
 *   for Split C.
 *
 *   Step 2. After the three trans calls plus [(w_sz _)] and the
 *           [xrutt_weaken_v1; exact: mix_ilsem_exportcall_ilsem_exportcall],
 *           you should see exactly these obligations (in some cyclic
 *           order):
 *
 *           [a] hRR for xrutt_weaken_v1     -> done.
 *           [b] hRAns                       -> use Eqdep UIP_refl (Section 5).
 *           [c] Sv.In (vid lp_rsp lp) callee_saved
 *                                            -> rewrite (lp_rspE ok_lp);
 *                                               exact: rsp_in_callee_saved.
 *           [d] Split C hpre                 -> by move=> i1 i3 ?; exists i1.
 *           [e] Split C hpost                -> destruct rcompose, subst,
 *                                               exact.
 *           [f] Split B hpre                 -> destruct hypothesis,
 *                                               choose i2' := i3, exact each
 *                                               half.
 *           [g] Split B hpost                -> destruct rcompose,
 *                                               substitute via sz_pre's
 *                                               [s1 = s2], take o3' := o2'.
 *           [h] Split A hpre                 -> construct
 *                                                 i2 := mkEstate (fscs i1)
 *                                                                (fmem i1)
 *                                                                (evm i3),
 *                                               then prove preF_ovm,
 *                                               preF_export, sz_pre as in
 *                                               Section 4.
 *           [i] Split A hpost                -> mirror
 *                                               [it_compiler_proof.v:828-994],
 *                                               adjusting field accesses.
 *
 *           Already-discharged tactics (lines 245-253) cover [d], [c],
 *           and parts of [b] (the REv side of xrutt_weaken_v1) and the
 *           two [done]s for hEE1/hEE2.
 *
 *   Step 3. Audit hint: after these edits, [Print Assumptions
 *           it_compiler_back_endP] should report only standard axioms
 *           ([Eqdep.Eq_rect_eq.eq_rect_eq] is acceptable as it is the
 *           only one introduced by UIP_refl, and is known to be
 *           consistent; see [Coq.Logic.Eqdep_dec]).
 *
 * ------------------------------------------------------------ *
 * 7. Useful in-scope facts and lemmas
 * ------------------------------------------------------------ *
 *
 *   Already pulled into the proof at lines 175-217:
 *     - [hexp        : it_merge_varmaps_proof.is_export sp fn]
 *     - [w_ovm       : merge_varmaps_export_call_checkP-typed equiv]
 *     - [w_lin       : linear_exportcallP haparams ok_lp]-typed equiv]
 *     - [hfd, fdexp, vtmp_not_magic, get_lfd_lp]
 *     - [zfd, ok_zfd, get_zfd]
 *     - [inv_info, inv_align, inv_tyin, inv_arg, inv_tyout, inv_res,
 *        inv_export, inv_cs, inv_stkmax, inv_framesize, inv_align_args]
 *     - [get_tfd, rip_eq, rsp_eq, globs_eq]   (tunneling)
 *     - [rip_eq', rsp_eq']                    (stack zeroization)
 *
 *   Useful lemmas (search by name in the indicated files):
 *     - [merge_varmaps_export_call_checkP]    [it_merge_varmaps_proof.v:1274]
 *     - [linear_exportcallP] (it variant)     [it_linearization_proof.v:4984]
 *     - [mix_ilsem_exportcall_ilsem_exportcall]  [linear_sem.v:720]
 *     - [istack_zeroization_lprogP_new]       [stack_zeroization_proof.v:690]
 *     - [wkequiv_io_trans]                    [relational_logic.v:2747]
 *     - [wkequiv_io_eutt_r]                   [relational_logic.v:2792]
 *     - [xrutt_weaken_v1]                     [proofs/itrees/xrutt_facts.v:684]
 *     - [compiler_back_end_meta print_linearP ok_lp]  -> [_, meta_rsp, _]
 *     - [tunnel_program_invariants ok_tp]     -> [rip_eq, [rsp_eq, [globs_eq, _]]]
 *     - [stack_zeroization_lprog_invariants ok_zp]  -> [rip_eq', rsp_eq', _]
 *     - [stack_zeroization_lfd_invariants ok_zfd]   -> [inv_info ... inv_align_args]
 *     - [linearization_proof.checked_prog ok_lp get_sfd]
 *     - [match_mem_read_incl_mem], [valid_stk] (fields of [match_mem])
 *     - [Eqdep.EqdepTheory.UIP_refl]          for the [hRAns] obligation
 *
 *   Pattern templates from the OLD proof (for direct adaptation):
 *     - Split A hpre allocatable / valid_between derivation:
 *       [it_compiler_proof.v:743-826]
 *     - Split A hpost values_uincl + match_mem + fscs + zeroized_s:
 *       [it_compiler_proof.v:828-994]
 *
 * ============================================================ *)

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
move=> h.
have [erip ersp egd] := compiler_back_end_meta print_linearP h.
move: h.
rewrite /compiler_back_end; t_xrbindP => ok_export checked_p lp ok_lp.
rewrite print_linearP => zp ok_zp.
rewrite print_linearP => tp' ok_tp.
rewrite print_linearP => ?; subst tp'.
move=> /InP ok_fn.

move: ok_export; rewrite /check_export /= => /allMP h.
have := h _ ok_fn; case hfd: get_fundef => [fd|//].
t_xrbindP=> fdexp.

set vtmp := var_tmps aparams.
have vtmp_not_magic : disjoint vtmp (magic_variables sp).
- exact: (var_tmp_not_magic (sip := sip_of_asm_e)) checked_p.

have get_lfd_lp :=
  get_fundef_p' (ep := ep_of_asm_e) (sip := sip_of_asm_e) ok_lp hfd.

have hexp : it_merge_varmaps_proof.is_export sp fn.
- by exists fd => //; move: fdexp => /is_RAnoneP.

have w_ovm := [elaborate
  merge_varmaps_export_call_checkP
  (p := sp) (global_data := rip) (fn := fn)
  checked_p hexp ] .

have cs_not_arr :
  forall x, Sv.In x one_varmap.callee_saved -> ~ is_aarr (vtype x).
- move=> x /sv_of_listP /mapP [/= r _ ->]; by case: r.

(* Linearization provides fd (sprog) and lfd_lp (lp-level). *)
have := [elaborate
  linear_exportcallP
    (hap_hlip haparams) vtmp_not_magic ok_lp cs_not_arr
    (gd := rip) (fn := fn) ].
rewrite /preF_export hfd get_lfd_lp => w_lin.

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

have w_mix := [elaborate mix_ilsem_exportcall_ilsem_exportcall lp fn ].

have w_sz :=
  istack_zeroization_lprogP_new
    (wE := wE) (rndE0_refl := RndE0Refl)
    (hap_hszp haparams)  _ ok_zp get_lfd_lp.

set lfd_lp := (linear_fd (ap_lip aparams) sp fn fd).2.
set szf := (fun fn0 : funname =>
  match stack_zero_info cparams fn0 with
  | Some (szs, ows) =>
      Some (szs, match ows with
                 | Some ws => ws
                 | None => match get_fundef (lp_funcs lp) fn0 with
                           | Some lfd0 => lfd_align lfd0
                           | None => U8
                           end
                 end)
  | None => None
  end).
apply: (wkequiv_io_trans
  (P23 := fun (i2 i3 : estate) =>
    preF_export sp lp rip fn i2 i3 /\ sz_pre lp lfd_lp i3 i3)
  (Q23 := fun (i2 i3 : estate) (o2 o3 : estate) =>
    exists o3', postF_export sp lp fn i2 i3 o2 o3'
             /\ sz_pos szf lp fn lfd_lp i3 i3 o3' o3)
  _ _ w_ovm); cycle 2.
apply: (wkequiv_io_trans
  (P23 := sz_pre lp lfd_lp)
  (Q23 := sz_pos szf lp fn lfd_lp)
  _ _ w_lin); cycle 2.
apply: (wkequiv_io_trans
  (P12 := eq) (P23 := sz_pre lp lfd_lp)
  (Q12 := fun _ _ => eq)
  _ _ _ (w_sz _)); cycle 2.
move=> s _ <-.
apply: (xrutt_weaken_v1
  (EE1 := errcutoff (is_error wE)) (EE2 := nocutoff)
  (EE1' := errcutoff (is_error wE)) (EE2' := nocutoff)); cycle 5.
exact: mix_ilsem_exportcall_ilsem_exportcall.
- done.
- done.
- move=> T1 T2 [e1|e1] [e2|e2] => //= -[?]; subst T1 => //= -[->].
  by move: e1 => [scs1 n1].
- move=> T1 T2 [[e1]|[scs1 n1]] // [scs1' a1] [[e2]|[scs2 n2]] // [scs2' a2].
  move=> [<- <-] a.
  by rewrite (Eqdep.EqdepTheory.UIP_refl _ _ a).
- done.
- rewrite (lp_rspE (sip := sip_of_asm_e) ok_lp); exact: rsp_in_callee_saved.
- by move=> i1 i3 ?; exists i1.
- by move=> i1 _ i3 o1 o3 <- hpresz [_ <-] hpossz.
- move=> i1 i3 [].
  rewrite /preF_export hfd  get_lfd_lp => -[hrsp hrip hinit hstk hvm hscs hmm].
  move=> [wrsp [hrsp' _ hstk' hval]].
  exists i3; first by split. by exists wrsp.
- by move=> i1 i2 i3 o1 o3 _ [w [_ ? _ _]] [r ??]; subst i2; exists r.
- move=> i1 i3 [hrsp hrip uvs mm hscs hinit halloc].
  exists {| escs := fscs i1; emem := fmem i1; evm := evm i3 |}.
  - split=> //=; rewrite hfd.
    rewrite -hrsp -hrip ersp erip.
    exists (lget_args (tunneling.tunnel_lfundef fn zfd) (evm i3)).
    split=> //=.
    by rewrite /lget_args /lget_vars /lfd_arg /= -inv_arg
      get_var_is_allow_undefined.
  rewrite /preF_export hfd get_lfd_lp; split.
  - rewrite -hrsp -hrip -rsp_eq rsp_eq' -rip_eq rip_eq'.
    split=> //=.
    + by move: hinit; rewrite -inv_cs /= fdexp.
  - move: halloc; rewrite /allocatable_stack /lfd_total_stack /tunneling.tunnel_lfundef /= -inv_export -inv_stkmax -inv_align /= fdexp.
    have /= := [elaborate (wunsigned_range (stack_limit (fmem i1)))].
    lia.
  exists (top_stack (fmem i1)); rewrite -hrsp -rsp_eq rsp_eq'.
  split=> //=.
  - move: halloc; rewrite /allocatable_stack /lfd_total_stack /tunneling.tunnel_lfundef /= -inv_export -inv_stkmax -inv_align /= fdexp.
    have /= := [elaborate (wunsigned_range (stack_limit (fmem i1)))].
    lia.
  have align_range : (wunsigned (top_stack (fmem i1)) - wsize_size (lfd_align lfd_lp) <
   wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) <=
   wunsigned (top_stack (fmem i1)))%Z.
  - have /= := [elaborate (align_word_range (lfd_align lfd_lp) (top_stack (fmem i1)))]. by [].
  have top_range : (0 <= wunsigned (top_stack (fmem i1)) < wbase Uptr)%Z.
  - have /= := [elaborate (wunsigned_range (top_stack (fmem i1)))]. by [].
  have stk_range : (0 <= wunsigned (stack_limit (fmem i1)) < wbase Uptr)%Z.
  - have /= := [elaborate (wunsigned_range (stack_limit (fmem i1)))]. by [].
  have halloc' :
    (0 <= lfd_stk_max lfd_lp + wsize_size (lfd_align lfd_lp) - 1 <=
     wunsigned (top_stack (fmem i1)) - wunsigned (stack_limit (fmem i1)))%Z.
  - move: halloc; rewrite /allocatable_stack /lfd_total_stack /tunneling.tunnel_lfundef /=.
    by rewrite -inv_export -inv_stkmax -inv_align /= fdexp /=.
  have! := (linearization_proof.checked_prog ok_lp hfd).
  rewrite /check_fd /=; t_xrbindP=> _ _ _ _ ok_stk_sz _ _ _.
  case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
  have hfb := frame_size_bound stk_sz_pos stk_extra_sz_pos.
  have lfd_stk_pos : (0 <= lfd_stk_max lfd_lp)%Z.
  - eapply Z.le_trans; last exact stk_frame_le_max.
    eapply Z.le_trans; last exact hfb. lia.
  have H6''' :
    (0 <= wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) - lfd_stk_max lfd_lp < wbase Uptr)%Z.
  - split.
    + lia.
    + have upper : (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) < wbase Uptr)%Z.
      * eapply Z.le_lt_trans; last exact (proj2 top_range).
        apply align_range.
      lia.
  have bottom_instack:
    zbetween
      (stack_limit (fmem i1))
      (wunsigned (top_stack (fmem i1)) - wunsigned (stack_limit (fmem i1)))
      (align_word (lfd_align lfd_lp) (top_stack (fmem i1))
       - wrepr Uptr (lfd_stk_max lfd_lp))%R
      (lfd_stk_max lfd_lp).
  - rewrite /zbetween !zify.
    rewrite wunsigned_sub //; lia.
  rewrite /valid_between.
  move=> pr /(zbetween_trans bottom_instack).
  rewrite -/(between _ _ _ _) -pointer_range_between => hpr.
  apply mm.(valid_stk).
  apply /pointer_rangeP.
  apply: pointer_range_incl_r hpr.
  exact: top_stack_below_root.
move=> i1 i2 i3 o1 o3 [hscs hmem] /=.
rewrite /preF_export /postF_export hfd get_lfd_lp.
move=> -[vs [hrsp hrip hget uvs]] [].
move=> [hrsp' hrip' hinit hstk hvm hscs' mm].
move=> [w [hrsp'' _ hw hvalid]].
move=> [r2 [hscs2 hmem2 [vs' [hvs' uvs']]]].
move=> [o3' []] [hrsp3 mm3 mu hscs3 sstb hz].
move=> [w' [hw' hscs3' hvm3 hmmz]].
move: hvs'; rewrite get_var_is_allow_undefined => -[?]; subst vs'.
rewrite -hmem2 in mm3.

split.
- (* values_uincl *)
  rewrite /lget_res /lget_vars /= -inv_res.
  suff heq : [seq (evm o3).[v_var x] | x <- lfd_res lfd_lp]
           = [seq (evm r2).[v_var x] | x <- lfd_res lfd_lp].
  + rewrite heq /= fdexp; exact: uvs'.
  apply map_ext => x hin.
  symmetry. admit. (* apply: hvm3. by apply /sv_of_listP /in_map; exists x.*)

- (* match_mem: combine hmem_o2 (match_mem fmem_o1 / emem_o2) with
     hmmz (match_mem_zero_export emem_o2 / emem_o3) *)
  move: hmmz; rewrite /match_mem_zero_export.
  case: szf => [[szs ows]|] /=; last first.
  + move=> <-; exact: mm3.
  move=> hmm; split.
  + move=> pr hb hval.
    have := mm3.(read_incl_mem) hb hval.
    rewrite hmm.(read_untouched) //.
    apply: not_between_U8_disjoint_zrange => //.
    admit.
    admit.
  + move=> pr w0 hb ok_w.
    (* hb says pr is in stack region of (fmem o1), but such pr is not valid,
       contradicting readV ok_w *)
    exfalso; apply/negP/(stack_region_is_free (m := fmem o1) (p := pr)).
    * by rewrite (readV ok_w).
    move: hb; rewrite /pointer_range.
    by rewrite -/(top_stack _); lia.
  + by move=> pr /mm3.(valid_incl); rewrite hmm.(valid_eq).
  move=> pr.
  rewrite -hmm.(valid_eq).
  by apply mm3.(valid_stk).
- by rewrite hscs2 hscs3 hscs3'.

set bottom : pointer := (align_word (lfd_align lfd_lp) (top_stack (fmem i1))
               - wrepr Uptr (lfd_stk_max lfd_lp))%R.

  have! := (linearization_proof.checked_prog ok_lp hfd).
  rewrite /check_fd /=; t_xrbindP=> _ _ _ _ ok_stk_sz _ _ _.
  case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
  have hfb := frame_size_bound stk_sz_pos stk_extra_sz_pos.
  have lfd_stk_pos : (0 <= lfd_stk_max lfd_lp)%Z.
  - eapply Z.le_trans; last exact stk_frame_le_max.
    eapply Z.le_trans; last exact hfb. lia.

move=> hi; move: hmmz; rewrite /match_mem_zero_export.
case hszs: szf => [[szs ows]|] //= hmm pr hnvalid.
case hb: (between bottom (lfd_stk_max lfd_lp) pr U8).
+ right. rewrite hmm.(read_zero) //. move: hb.
  rewrite /bottom /=.
  admit.

left; rewrite -hmm.(read_untouched); last first.
+ apply not_between_U8_disjoint_zrange => //.
  * admit.
  admit. (* by apply /negP /negPf. *)
rewrite -mu //.
- apply/negP; by rewrite -hmem.
(* ~ pointer_range (sp0 - wrepr max0) sp0 pr *)
move: hszs ok_zfd; rewrite /szf /stack_zeroization_lfd => ->.
have lp_export' : lfd_export lfd_lp && (0 <? lfd_stk_max lfd_lp)%Z =
                  (0 <? lfd_stk_max lfd_lp)%Z
  by rewrite /= fdexp.
rewrite lp_export' /=.
case: ZltP => [Hmaxpos | Hmaxnpos]; last first.
{ (* lfd_stk_max = 0: range is empty *)
  move=> _.
  have Hmax0 : sf_stk_max (f_extra fd) = 0%Z.
  { rewrite /= in inv_stkmax; rewrite inv_stkmax.
    apply: Z.le_antisymm; last first.
    - move: lfd_stk_pos. by rewrite -inv_stkmax.
    rewrite -inv_stkmax. exact/Z.nlt_ge/Hmaxnpos. }
  rewrite Hmax0 wrepr0 GRing.subr0.
  rewrite /pointer_range; move=> /andP [/ZleP Ha /ZltP Hb]; lia. }
rewrite /stack_zeroization_lfd_body; t_xrbindP => halign _ _ _ _ _.
have Hframe_eq : lfd_frame_size lfd_lp = (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z.
  admit. (* rewrite  /frame_size inv_framesize /=. *)
have Hsum_nn : (0 <= sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z
  := Z.add_nonneg_nonneg _ _ stk_sz_pos stk_extra_sz_pos.
have Hws : (0 < wsize_size (sf_align (f_extra fd)))%Z := wsize_size_pos _.
have Hmax_le_top : (sf_stk_max (f_extra fd) <= wunsigned (top_stack (fmem i1)))%Z.
  apply: (Z.le_trans _ (lfd_stk_max lfd_lp + wsize_size (lfd_align lfd_lp) - 1)%Z).
  + admit. (* hw *)
  admit. (*rewrite inv_stkmax /=.
  generalize (wsize_size_pos (lfd_align lfd_lp)). clear. intros. lia.*)

have top_range : (0 <= wunsigned (top_stack (fmem i1)) < wbase Uptr)%Z
  by have /= := [elaborate (wunsigned_range (top_stack (fmem i1)))].

have Hsum_le_top : (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) <=
                    wunsigned (top_stack (fmem i1)))%Z.
  apply: (Z.le_trans _ _ _ hfb).
  apply: (Z.le_trans _ _ _ stk_frame_le_max Hmax_le_top).

have align_range : (wunsigned (top_stack (fmem i1)) - wsize_size (lfd_align lfd_lp) <
 wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) <=
 wunsigned (top_stack (fmem i1)))%Z
  by have /= := [elaborate (align_word_range (lfd_align lfd_lp) (top_stack (fmem i1)))].
have halloc_lp :
  (0 <= lfd_stk_max lfd_lp + wsize_size (lfd_align lfd_lp) - 1 <=
   wunsigned (top_stack (fmem i1)) - wunsigned (stack_limit (fmem i1)))%Z.
- have := wsize_size_pos (lfd_align lfd_lp).
  admit. (* halloc_lin *)

have Hrng : (0 <= wunsigned (top_stack (fmem i1)) -
             (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)) < wbase Uptr)%Z.
  split.
  - generalize Hsum_le_top. clear. intros. lia.
  - generalize top_range Hsum_nn. clear. intros. lia.
have Halign_final :
  is_align (Pointer := WArray.PointerZ)
    (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z (sf_align (f_extra fd)).
  by move: halign; rewrite Hframe_eq.
rewrite /align_top_stack -hmem
  ([elaborate align_top_aligned Hsum_nn Hrng Halign_final]).
rewrite pointer_range_between.
have Hbottom_eq :
  (align_word (lfd_align lfd_lp) (top_stack (fmem i1)) -
   wrepr Uptr (sf_stk_max (f_extra fd)))%R = bottom.
  by rewrite /bottom /=.
rewrite Hbottom_eq.
have Hsize_eq :
  (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))) -
   wunsigned bottom)%Z = lfd_stk_max lfd_lp.
  rewrite /bottom wunsigned_sub; last first.
  - split. admit. (* first exact: (proj1 H6''').*)
    apply: (Z.le_lt_trans _ (wunsigned (top_stack (fmem i1)))); last exact (proj2 top_range).
    apply: (Z.le_trans _ (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1))))).
    + generalize lfd_stk_pos. clear. intros. lia.
    + apply (proj2 align_range).
  generalize (wunsigned (align_word (lfd_align lfd_lp) (top_stack (fmem i1)))) (lfd_stk_max lfd_lp).
  clear. intros. lia.
rewrite Hsize_eq.
by apply/negP; rewrite hb.

Admitted.

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
have {}h_be := lutt_xrutt_trans_r (hinv _ _ _) h_be.
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
