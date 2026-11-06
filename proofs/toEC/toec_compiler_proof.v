(* * The extraction for safety and the compiler, composed.

   [jasmin2ec] extracts a Jasmin program [up] for safety with
   [toec_uprog_safety], which gives [p'], printed in EasyCrypt; its first
   passes ([toec_uprog_common]) give [pc], the machine words annotated [wint]
   being turned into integers when [wi2i] holds. The compiler compiles [up]
   itself into the assembly program [xp].

   [toec_compiler_tgt_src]: for an export function [fn], every run of [p']
   in the semantics of EasyCrypt (the mode [total_init], the assertions
   evaluated, the contracts not) that does not fail, from arguments related
   to the initial state of [xp], corresponds to a run of [xp] that does not
   fail. The results are related through the run of [up] that links them:
   - [safety_wi_pre], [safety_wi_post]: the arguments and results of [p']
     are those of [pc], up to the masks of the arrays and to the positions
     that [dead_args] keeps ([safety_spec]), and those of [pc] are those of
     [up], the words annotated [wint] being read as integers when [wi2i]
     holds ([common_rel]);
   - [full_pre], [full_post]: those of [up] and the assembly state, as in
     [it_compile_prog_to_asmP].
   It composes [toec_uprog_safety_tgt_src] (from [p'] to [up]) and
   [it_compile_prog_to_asmP] (from [up] to [xp]). Each of them states that
   the run on its right does not fail when the run on its left does not fail
   ([wkequiv_io]), so that they compose by [wkequiv_io_trans].

   [toec_compiler_scalars_tgt_src] is the case, with [wi2i_prog], of a
   function whose
   parameters and results are not arrays and whose signature [dead_args]
   keeps (the variables are protected, as those of the export functions are
   in [Compile.do_toec_safety]): the arguments and the results of [p'] are
   those of [up], the words annotated [wint] being read as integers, and are
   defined. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From ITree Require ITree.
Require Import compiler_util psem psem_facts relational_logic.
Require Import safety_common wint_int wint_int_proof.
Require Import toec_prog explicit_init simplify_asserts assert_facts dead_args.
Require Import explicit_init_proof dead_code_total_proof dead_args_proof toec_safety_proof.
Require Import arch_decl arch_extra arch_sem sem_params_of_arch_extra compiler it_compiler_proof.

Section PROOF.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {sc_sem : syscall.syscall_sem syscall_state}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {vregs : veneer_regs_info} {avs : asm_veneer_sem}
  (aparams : arch_params.architecture_params)
  (haparams : arch_params_proof.h_architecture_params aparams)
  (cparams : compiler_params)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p).

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance with_Error0.
#[local] Existing Instance HandlerContract.

(* The semantics of EasyCrypt: the mode [total_init], the assertions
   evaluated, the contracts not; the other parameters are those of the
   source of the compiler ([isem_unit]). *)
Definition isem_ec (p : uprog) (fn : funname) (fs : fstate) :
  ITreeDefinition.itree ErrEvent fstate :=
  it_sems_core.isem_fun
    (asm_op := extended_op) (ep := ep_of_asm_e) (spp := spp_of_asm_e)
    (wa := withassert_nocontract) (sm := total_init) (sip := sip_of_asm_e)
    (scP := sCP_unit) (wE := with_Error0) (wsw := nosubword) (dc := indirect_c)
    (pT := progUnit) p tt fn fs.

(* The parameters of [Compile.do_toec_safety]. *)
Context
  (fresh_var_ident fresh_copy_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (mask : var -> var)
  (protect : funname -> var -> bool)
  (dead_info : (funname -> var -> bool) -> _uprog ->
               funname -> option (seq bool) * option (seq bool))
  (get_info : _uprog -> Sv.t * (var -> option (signedness * var))).

(* No instruction of the architecture outputs an array: [is_not_carr_ltype]
   for the base instructions, the extra ones of each architecture. *)
Hypothesis asm_op_tout :
  forall o : extended_op, all is_not_carr (map eval_atype (tout (asm_op_instr o))).

Section FN.

Context (wi2i : bool) (up : uprog) (xp : asm_prog) (info : keep_info) (p8 : uprog)
  (fn : funname) (fsig : seq (extended_type Z) * seq (extended_type Z)) (xfd : asm_fundef).

(* The arguments [fs'] of [p'] and the initial state [t] of [xp] are related
   through arguments [fs] of [up]. *)
Definition toec_pre (fs' : fstate) (t : asmmem) : Prop :=
  exists2 fs, safety_wi_pre wi2i info p8 fsig fn fn fs' fs & full_pre up xp fn xfd fs t.

Definition toec_post (fs' : fstate) (t : asmmem) (fr' : fstate) (t' : asmmem) : Prop :=
  exists fs fr,
    [/\ safety_wi_pre wi2i info p8 fsig fn fn fs' fs,
        full_pre up xp fn xfd fs t,
        safety_wi_post wi2i info p8 fsig fn fn fs' fs fr' fr
      & full_post cparams up xp fn xfd fs t fr t'].

(* Without arrays and with the signature kept by [dead_args]: the arguments
   [fs'] of [p'] are those of [up] read through [wi2i], they are defined and
   have the types of the parameters of [p8]. *)
Definition toec_scalars_pre (fs' : fstate) (t : asmmem) : Prop :=
  exists fs,
    [/\ fs_rel (vs_pre fsig.1) fs' fs,
        all is_defined (fvals fs'),
        forall fd8, get_fundef (p_funcs p8) fn = Some fd8 ->
          is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd8.(f_tyin)) (fvals fs'))
      & full_pre up xp fn xfd fs t].

Definition toec_scalars_post (fs' : fstate) (t : asmmem) (fr' : fstate) (t' : asmmem) : Prop :=
  exists fs fr,
    [/\ fs_rel (vs_pre fsig.1) fs' fs,
        full_pre up xp fn xfd fs t,
        fs_rel (vs_post fsig.2) fr' fr,
        all is_defined (fvals fr')
      & full_post cparams up xp fn xfd fs t fr t'].

End FN.

(* For an export function [fn] of [up], every run of [p'] in the semantics
   of EasyCrypt that does not fail corresponds to a run of [xp] that does not
   fail, with results related through a run of [up]. The masks are fresh in
   the program that [explicit_init] receives and the input of [dead_args] is
   well typed, as in [toec_uprog_safety_tgt_src]. *)
Theorem toec_compiler_tgt_src (wi2i : bool) entries (up p' : uprog) xp fn fd :
  toec_uprog_safety fresh_var_ident get_info fresh_copy_ident wi2i mask protect dead_info up
    = ok p' ->
  compile_prog_to_asm aparams cparams entries up = ok xp ->
  fn \in entries ->
  get_fundef (p_funcs up) fn = Some fd ->
  let fsig := (build_sig (get_info up).2 (fn, fd)).2 in
  exists p5 p6 info xfd,
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  [/\ toec_uprog_pre_init fresh_var_ident fresh_copy_ident get_info wi2i up = ok p5,
      explicit_init_prog mask p5 = ok p6,
      dead_args_info (LC := toec_LoopCounter) protect (dead_info protect) p8 = ok (p', info),
      get_fundef xp.(asm_funcs) fn = Some xfd,
      xfd.(asm_fd_export) &
      mask_ok mask p5 -> total_ok p8 ->
      wkequiv_io
        (toec_pre wi2i up xp info p8 fn fsig xfd)
        (isem_ec p' fn)
        (isem_asm xp fn)
        (toec_post wi2i up xp info p8 fn fsig xfd)].
Proof using asm_op_tout haparams print_linearP print_sprogP print_uprogP.
  move=> hp' hxp hfn hfd fsig.
  have [p5 [p6 [info [h5 h6 h9 hsafe]]]] :=
    toec_uprog_safety_tgt_src (asm_op := extended_op) (ep := ep_of_asm_e) (spp := spp_of_asm_e)
      (sip := sip_of_asm_e) (E := ErrEvent) (wE := with_Error0) (rE := HandlerContract)
      (rE_trans := HandlerContract_trans) tt asm_op_tout hp'.
  have [xfd [hxfd hexp hcomp]] :=
    it_compile_prog_to_asmP haparams print_uprogP print_sprogP print_linearP hxp hfn.
  exists p5, p6, info, xfd; split => // hmask hok.
  apply: (wkequiv_io_trans (rE12 := HandlerContract) (rE23 := HandlerContract)
            (rE_trans := HandlerContract_trans) _ _ (hsafe hmask hok fn fd hfd) hcomp).
  - by move=> fs' t [fs hp1 hp2]; exists fs.
  by move=> fs' fs t fr' t' hp1 hp2 [fr hq1 hq2]; exists fs, fr.
Qed.

(* ------------------------------------------------------------------------- *)
(* Functions without arrays in their signature                              *)

Definition not_arr_ety (ety : extended_type Z) : bool :=
  if ety is ETarr _ _ then false else true.

(* The values given for a signature without arrays, read through [wi2i],
   are not arrays. *)
Lemma vs_scalars (fsig : seq (extended_type Z)) vsi vs :
  all not_arr_ety fsig ->
  List.Forall2 (fun ety v => exists2 ty, type_of_val v = eval_atype ty &
                 esubtype ety (to_etype (sign_of_etype ety) ty)) fsig vs ->
  vsi = map2 (fun ety v => val_to_int (sign_of_etype ety) v) fsig vs ->
  all (fun v => ~~ is_carr (type_of_val v)) vsi.
Proof.
  move=> + hF ->; elim: hF => //= ety v fsig' vs' [ty hty hsub] _ ih /andP [hety /ih ->].
  rewrite andbT; case: v hty => //=.
  - move=> len _; case: ty hsub => //= ws len' hsub _.
    by case: ety hety hsub => //= -[].
  - by move=> ws w _; case: sign_of_etype.
  move=> t hu _; case: t hu => //=.
  by move=> ws hu; case: sign_of_etype.
Qed.

Lemma not_arr_fsig (m : var -> option (signedness * var)) (xs : seq var_i) tys :
  all (fun ty => is_not_carr (eval_atype ty)) tys ->
  all not_arr_ety (map2 (fun (x : var_i) ty => to_etype (Option.map fst (m x)) ty) xs tys).
Proof. by elim: xs tys => [|x xs ih] [|ty tys] //= /andP [+ /ih ->]; case: ty. Qed.

(* For an export function [fn] of [up] whose parameters and results are not
   arrays and whose variables are protected, the arguments and the results of
   [p'] are those of [up], read through [wi2i]. *)
Theorem toec_compiler_scalars_tgt_src entries (up p' : uprog) xp fn fd :
  toec_uprog_safety fresh_var_ident get_info fresh_copy_ident true mask protect dead_info up
    = ok p' ->
  compile_prog_to_asm aparams cparams entries up = ok xp ->
  fn \in entries ->
  get_fundef (p_funcs up) fn = Some fd ->
  all (fun ty => is_not_carr (eval_atype ty)) fd.(f_tyin) ->
  all (fun ty => is_not_carr (eval_atype ty)) fd.(f_tyout) ->
  (forall x, protect fn x) ->
  let fsig := (build_sig (get_info up).2 (fn, fd)).2 in
  exists p5 p6 xfd,
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  [/\ toec_uprog_pre_init fresh_var_ident fresh_copy_ident get_info true up = ok p5,
      explicit_init_prog mask p5 = ok p6,
      get_fundef xp.(asm_funcs) fn = Some xfd,
      xfd.(asm_fd_export) &
      mask_ok mask p5 -> total_ok p8 ->
      wkequiv_io
        (toec_scalars_pre up xp p8 fn fsig xfd)
        (isem_ec p' fn)
        (isem_asm xp fn)
        (toec_scalars_post up xp fn fsig xfd)].
Proof using asm_op_tout haparams print_linearP print_sprogP print_uprogP.
  move=> hp' hxp hfn hfd htyin htyout hpr fsig.
  have [p5 [p6 [info [xfd]]]] := toec_compiler_tgt_src hp' hxp hfn hfd.
  move=> /= [h5 h6 h9 hxfd hexp hall]; exists p5, p6, xfd; split => // hmask hok.
  have [hkp hkr] :=
    dead_args_info_protected (asm_op := extended_op)
      (sip := @sip_of_asm_e _ _ _ _ _ _ _ asm_e syscall_state sc_sem) hpr h9.
  have hkeep k fs : all id k -> fs_keep k fs = fs.
  - case: fs => scs m vs hk; rewrite /fs_keep /=; congr Build_fstate.
    by elim: k vs hk => [|[] k ih] [|v vs] //= /ih ->.
  have hsig1 : all not_arr_ety fsig.1.
  - by rewrite /fsig; case: (fd) htyin => /= ????????; apply: not_arr_fsig.
  have hsig2 : all not_arr_ety fsig.2.
  - by rewrite /fsig; case: (fd) htyout => /= ????????; apply: not_arr_fsig.
  apply: wkequiv_io_weaken (hall hmask hok) => //.
  - move=> fs' t [fs [hpre hdef hty hfull]]; exists fs => //; exists fs' => //; split => //.
    exists fs'.
    + case: hpre => _ _ [hF hvs]; split => //.
      apply/mask_vals_scalarsE; last by [].
      by apply: vs_scalars hsig1 hF hvs.
    by split => //; rewrite hkeep.
  move=> fs' t fr' t' _
    [fs [fr [_ hp3 [fsi [fri [[_ [fsm hm [hfs _]]] hp2 [frm hm' hfr] hq2]]] hq3]]].
  have hesub ety : esubtype ety ety.
  - case: ety => //=.
    by move=> [sg|] w; rewrite ?eqxx // cmp_le_refl.
  case: hq2 => hscs hmem [hF hvs].
  have hfri : all (fun v => ~~ is_carr (type_of_val v)) (fvals fri).
  - apply: vs_scalars hsig2 _ hvs.
    by apply: List.Forall2_impl hF => ety v [ty h1 h2]; exists ty => //; rewrite -h2.
  have hmaskE f1 f2 : all (fun v => ~~ is_carr (type_of_val v)) (fvals f2) ->
    mask_fs f1 f2 -> f1 = f2 /\ all is_defined (fvals f2).
  - case: f1 f2 => scs1 m1 vs1 [scs2 m2 vs2] /= h [/= -> ->] /(mask_vals_scalarsE _ h) [-> ->].
    by [].
  have hfsi : all (fun v => ~~ is_carr (type_of_val v)) (fvals fsi).
  - by case: hp2 => _ _ [hFi hvsi]; apply: vs_scalars hsig1 hFi hvsi.
  have [? _] := hmaskE _ _ hfsi hm; subst fsm.
  have [? hdef] := hmaskE _ _ hfri hm'; subst frm.
  rewrite hkeep // in hfs; rewrite hkeep // in hfr; subst fs' fr'.
  by exists fs, fr; split => //; split.
Qed.

End PROOF.
