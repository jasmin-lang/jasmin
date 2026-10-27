(* * Correctness of the two extractions through the passes of the extraction
   for safety ([toec_prog]).

   The semantics of the extracted programs is that of EasyCrypt: the mode
   [total_init] (every access succeeds and every output of an instruction is
   defined), the assertions evaluated, the contracts not
   ([withassert_nocontract]). The semantics of the source is the partial
   mode, with the assertions and the contracts evaluated ([withassert]).

   - [toec_uprog_safety_tgt_src]: every run of the result of the extraction
     for safety that does not fail corresponds to a run of the source that
     does not fail, with related arguments and results ([safety_spec]).
   - [toec_uprog_via_safety_src_tgt]: every run of the source that does not
     fail is matched by a run of the result of the plain extraction through
     the passes of the extraction for safety, with related arguments and
     results ([via_safety_spec]). Its direction is that of [drop_asserts],
     which holds only from the program with assertions to the one without.

   Both compose the correctness of each pass. The statements on the masks of
   [explicit_init] ([mask_ok]) and the well-typedness that [dead_args] needs
   ([total_ok]) are on the programs these passes receive. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import toec_for toec_while normalize_calls contracts_to_asserts safety explicit_init
  simplify_asserts assert_facts dead_code dead_args drop_asserts drop_removable toec_prog.
Require Import normalize_calls_proof contracts_to_asserts_proof safety_proof
  toec_while_proof toec_for_proof explicit_init_proof simplify_asserts_proof
  assert_facts_proof dead_code_total_proof dead_args_proof drop_asserts_proof
  drop_removable_proof.

Section PROOF.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Context
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE : EventRels E0}
  {rE_trans : EventRels_trans rE rE rE}.

Notation wiequiv_f_ wa1 wa2 sm1 sm2 :=
  (wiequiv_f (wa1 := wa1) (wa2 := wa2) (sm1 := sm1) (sm2 := sm2)).

(* [wiequiv_f_trans] in any modes. *)
Lemma wiequiv_f_trans_sm {wa1 wa2 wa3 : WithAssert} {sm1 sm2 sm3 : SemMode}
  (p1 p2 p3 : uprog) (ev : extra_val_t) fn (S12 S23 S13 : EquivSpec) :
  (forall fs1 fs3, rpreF (eS := S13) fn fn fs1 fs3 ->
     exists2 fs2, rpreF (eS := S12) fn fn fs1 fs2 & rpreF (eS := S23) fn fn fs2 fs3) ->
  (forall fs1 fs2 fs3 r1 r2 r3,
     rpreF (eS := S12) fn fn fs1 fs2 -> rpreF (eS := S23) fn fn fs2 fs3 ->
     rpostF (eS := S12) fn fn fs1 fs2 r1 r2 -> rpostF (eS := S23) fn fn fs2 fs3 r2 r3 ->
     rpostF (eS := S13) fn fn fs1 fs3 r1 r3) ->
  wiequiv_f_ wa1 wa2 sm1 sm2 p1 p2 ev ev (rpreF (eS := S12)) fn fn (rpostF (eS := S12)) ->
  wiequiv_f_ wa2 wa3 sm2 sm3 p2 p3 ev ev (rpreF (eS := S23)) fn fn (rpostF (eS := S23)) ->
  wiequiv_f_ wa1 wa3 sm1 sm3 p1 p3 ev ev (rpreF (eS := S13)) fn fn (rpostF (eS := S13)).
Proof using rE_trans.
  move=> hpre hpost; apply: wkequiv_io_trans => //.
  by move=> > h12 h23 [r2 ??]; apply: hpost h12 h23 _ _; eauto.
Qed.

Lemma wiequiv_f_trans_eq_r {wa1 wa2 wa3 : WithAssert} {sm1 sm2 sm3 : SemMode}
  (p1 p2 p3 : uprog) (ev : extra_val_t) fn (S : EquivSpec) :
  wiequiv_f_ wa1 wa2 sm1 sm2 p1 p2 ev ev (rpreF (eS := S)) fn fn (rpostF (eS := S)) ->
  wiequiv_f_ wa2 wa3 sm2 sm3 p2 p3 ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)) ->
  wiequiv_f_ wa1 wa3 sm1 sm3 p1 p3 ev ev (rpreF (eS := S)) fn fn (rpostF (eS := S)).
Proof using rE_trans.
  apply: wiequiv_f_trans_sm.
  - by move=> fs1 fs3 h; exists fs3.
  by move=> > _ [_ <-] + <-.
Qed.

Lemma wiequiv_f_trans_eq_l {wa1 wa2 wa3 : WithAssert} {sm1 sm2 sm3 : SemMode}
  (p1 p2 p3 : uprog) (ev : extra_val_t) fn (S : EquivSpec) :
  wiequiv_f_ wa1 wa2 sm1 sm2 p1 p2 ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)) ->
  wiequiv_f_ wa2 wa3 sm2 sm3 p2 p3 ev ev (rpreF (eS := S)) fn fn (rpostF (eS := S)) ->
  wiequiv_f_ wa1 wa3 sm1 sm3 p1 p3 ev ev (rpreF (eS := S)) fn fn (rpostF (eS := S)).
Proof using rE_trans.
  apply: wiequiv_f_trans_sm.
  - by move=> fs1 fs3 h; exists fs1.
  by move=> > [_ <-] _ <-.
Qed.

Context
  (fresh_var_ident fresh_removable_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Context (ev : extra_val_t).

(* From the output of [sc_prog], in the total mode and with the assertions
   evaluated, to the source, in the partial mode and with the assertions and
   the contracts evaluated. *)
Lemma sc_front_tgt_src (p p1 p2 p3 : uprog) fn :
  normalize_calls_prog fresh_var_ident p = ok p1 ->
  contracts_to_asserts_prog fresh_removable_ident p1 = ok p2 ->
  sc_prog p2 = ok p3 ->
  wiequiv_f_ withassert_nocontract withassert total partial p3 p ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using rE_trans.
  move=> h1 h2 h3.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := partial) (p2 := p2)).
  - exact: (safety_callP (spp := spp) (wa := withassert_nocontract) (rE := rE) erefl ev h3).
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert) (sm2 := partial) (p2 := p1)).
  - exact: (contracts_to_asserts_tgt_src (sm := partial) (rE := rE) ev h2).
  exact: (normalize_calls_l ev h1).
Qed.

Context (mask : var -> var).

(* No instruction of the architecture outputs an array ([is_not_carr_ltype] in
   [arch_extra.v]). *)
Hypothesis asm_op_tout :
  forall o : asm_op_t, all is_not_carr (map eval_atype (tout (asm_op_instr o))).

(* From the output of [explicit_init], in the mode [total_init], to the output
   of [sc_prog], in the total mode, both with the assertions evaluated. *)
Lemma ei_tgt_src (p3 p5 p6 : uprog) fn :
  toec_for_prog fresh_var_ident (toec_while_prog p3) = ok p5 ->
  mask_ok mask p5 ->
  explicit_init_prog mask p5 = ok p6 ->
  wiequiv_f_ withassert_nocontract withassert_nocontract total_init total p6 p3 ev ev
    (rpreF (eS := mask_spec)) fn fn (rpostF (eS := mask_spec)).
Proof using asm_op_tout rE_trans.
  move=> h5 [hinj hfresh htype hcontract] h6.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total) (p2 := p5)).
  - exact: (explicit_init_callP (wa := withassert_nocontract) erefl ev
              hinj hfresh htype hcontract asm_op_tout h6).
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total)
           (p2 := toec_while_prog p3)).
  - exact: (toec_for_l (wa := withassert_nocontract) (sm := total) (rE := rE) ev h5).
  exact: (toec_while_l (wa := withassert_nocontract) (sm := total) (rE := rE) p3 ev).
Qed.

Context (protect : funname -> var -> bool).
Context (dead_info : (funname -> var -> bool) -> _uprog ->
                     funname -> option (seq bool) * option (seq bool)).

(* From the output of [dead_args] to the output of [explicit_init], both in
   the mode [total_init] with the assertions evaluated. *)
Lemma dead_tgt_src {LC : LoopCounter} (p6 p9 : uprog) info fn :
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  total_ok p8 ->
  dead_args_info protect (dead_info protect) p8 = ok (p9, info) ->
  wiequiv_f_ withassert_nocontract withassert_nocontract total_init total_init p9 p6 ev ev
    (rpreF (eS := dead_args_tgt_src_spec info p8)) fn fn
    (rpostF (eS := dead_args_tgt_src_spec info p8)).
Proof using rE_trans.
  move=> p8 hok h9.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total_init) (p2 := p8)).
  - exact: (dead_args_tgt_src (rE := rE) ev hok h9).
  apply: (wiequiv_f_trans_eq_l (wa2 := withassert_nocontract) (sm2 := total_init)
           (p2 := simplify_asserts_prog p6)).
  - exact: (assert_facts_tgt_src (rE := rE)).
  exact: (simplify_asserts_tgt_src (rE := rE)).
Qed.

(* The relation between a run of the result of the extraction for safety and
   a run of the source: the arguments given to the source are those given to
   the result, plus the removed ones, once the masks that [explicit_init]
   adds after the arrays are dropped; the masks describe the initialisation
   of the arrays and the scalars are defined; the arguments have the types of
   the parameters of [p8], the input of [dead_args]. The results are related
   in the same way. *)
Definition safety_spec (info : keep_info) (p8 : uprog) : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs' fs =>
       fn1 = fn2 /\
       exists2 fsm, mask_fs fsm fs &
         fs' = fs_keep (kparams info fn1) fsm /\
         forall fd, get_fundef (p_funcs p8) fn1 = Some fd ->
           is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fsm))
   ; rpostF_ := fun fn1 _ _ _ fr' fr =>
       exists2 frm, mask_fs frm fr & fr' = fs_keep (kres info fn1) frm |}.

Lemma safety_chain_tgt_src {LC : LoopCounter} (p p1 p2 p3 p5 p6 p9 : uprog) info fn :
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  normalize_calls_prog fresh_var_ident p = ok p1 ->
  contracts_to_asserts_prog fresh_removable_ident p1 = ok p2 ->
  sc_prog p2 = ok p3 ->
  toec_for_prog fresh_var_ident (toec_while_prog p3) = ok p5 ->
  mask_ok mask p5 ->
  explicit_init_prog mask p5 = ok p6 ->
  total_ok p8 ->
  dead_args_info protect (dead_info protect) p8 = ok (p9, info) ->
  wiequiv_f_ withassert_nocontract withassert total_init partial p9 p ev ev
    (rpreF (eS := safety_spec info p8)) fn fn (rpostF (eS := safety_spec info p8)).
Proof using asm_op_tout rE_trans.
  move=> p8 h1 h2 h3 h5 hmask h6 hok h9.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total) (p2 := p3));
    last first.
  - exact: sc_front_tgt_src h1 h2 h3.
  apply: (wiequiv_f_trans_sm (wa2 := withassert_nocontract) (sm2 := total_init) (p2 := p6)).
  3: exact: dead_tgt_src hok h9.
  3: exact: ei_tgt_src h5 hmask h6.
  - move=> fs1 fs3 /= [_ [fsm hm [-> hty]]]; exists fsm => //.
  by move=> fs1 fs2 fs3 r1 r2 r3 _ _ /= -> hm; exists r2.
Qed.

(* The program that [explicit_init] receives in [toec_uprog_assert]. *)
Definition toec_uprog_pre_init (p : _uprog) : cexec _uprog :=
  Let p := normalize_calls_prog (pT := progUnit) fresh_var_ident p in
  Let p := contracts_to_asserts_prog fresh_removable_ident p in
  Let p := sc_prog p in
  toec_for_prog (pT := progUnit) fresh_var_ident (toec_while_prog (pT := progUnit) p).

(* Every run of the result of the extraction for safety, in the semantics of
   EasyCrypt (the mode [total_init], the assertions evaluated, the contracts
   not), that does not fail corresponds to a run of the source, in the
   partial mode with its assertions and its contracts evaluated, that does
   not fail and computes the same results, up to [safety_spec]. The masks
   are fresh in the program that [explicit_init] receives, and the input of
   [dead_args] is well typed ([total_ok]). *)
Theorem toec_uprog_safety_tgt_src (p p' : uprog) :
  toec_uprog_safety fresh_var_ident fresh_removable_ident mask protect dead_info p = ok p' ->
  exists p5 p6 info,
  [/\ toec_uprog_pre_init p = ok p5,
      explicit_init_prog mask p5 = ok p6 &
      let p8 := assert_facts_prog (simplify_asserts_prog p6) in
      mask_ok mask p5 -> total_ok p8 ->
      forall fn,
      wiequiv_f_ withassert_nocontract withassert total_init partial p' p ev ev
        (rpreF (eS := safety_spec info p8)) fn fn (rpostF (eS := safety_spec info p8))].
Proof using asm_op_tout rE_trans.
  rewrite /toec_uprog_safety /toec_uprog_assert /dead_args_prog /toec_uprog_pre_init.
  t_xrbindP => p6 p1 h1 p2 h2 p3 h3 p5 h5 h6 r h9 <-.
  case: r h9 => p9 info h9; exists p5, p6, info; split => //.
  - by rewrite h1 /= h2 /= h3.
  by move=> hmask hok fn; apply: safety_chain_tgt_src h1 h2 h3 h5 hmask h6 hok h9.
Qed.

(* From the source, in the partial mode with its assertions and its contracts
   evaluated, to the input of [explicit_init], in the total mode with the
   assertions evaluated. *)
Lemma pre_init_src_tgt (p p1 p2 p3 p5 : uprog) fn :
  normalize_calls_prog fresh_var_ident p = ok p1 ->
  contracts_to_asserts_prog fresh_removable_ident p1 = ok p2 ->
  sc_prog p2 = ok p3 ->
  toec_for_prog fresh_var_ident (toec_while_prog p3) = ok p5 ->
  wiequiv_f_ withassert withassert_nocontract partial total p p5 ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using rE_trans.
  move=> h1 h2 h3 h5.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert) (sm2 := partial) (p2 := p1)).
  - exact: (normalize_calls_src_tgt (wa := withassert) (rE := rE) ev h1).
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := partial) (p2 := p2)).
  - exact: (contracts_to_asserts_src_tgt (sm := partial) (rE := rE) ev h2).
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total) (p2 := p3)).
  - exact: (safety_src_tgt (spp := spp) (wa := withassert_nocontract) (wE := wE) (rE := rE)
              ev erefl h3).
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total)
           (p2 := toec_while_prog p3)).
  - exact: (toec_while_src_tgt (spp := spp) (wa := withassert_nocontract)
              (wE := wE) (rE := rE) p3 ev).
  exact: (toec_for_src_tgt (spp := spp) (wa := withassert_nocontract)
            (wE := wE) (rE := rE) ev h5).
Qed.

Context (removable : var -> bool).

(* The relation between a run of the source and a run of the result of the
   plain extraction through the passes of the extraction for safety: the
   arguments given to the result are those given to the source followed, for
   the arrays, by masks that describe their initialisation, but those that
   [drop_removable] removes from [p7], its input; the scalars are defined.
   The results are related in the same way. *)
Definition via_safety_spec (p7 : uprog) : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs fs' =>
       fn1 = fn2 /\
       exists2 fsm, mask_fs fsm fs & fs' = fs_keep (rmv_keep_params removable p7 fn1) fsm
   ; rpostF_ := fun fn1 _ _ _ fr fr' =>
       exists2 frm, mask_fs frm fr & fr' = fs_keep (rmv_keep_res removable p7 fn1) frm |}.

(* From the input of [explicit_init], in the total mode, to the result of
   [drop_removable], in the mode [total_init], both with the assertions
   evaluated. *)
Lemma ei_drop_src_tgt (p5 p6 p8 : uprog) fn :
  mask_ok mask p5 ->
  explicit_init_prog mask p5 = ok p6 ->
  drop_removable_prog removable (drop_asserts_prog p6) = ok p8 ->
  wiequiv_f_ withassert_nocontract withassert_nocontract total total_init p5 p8 ev ev
    (rpreF (eS := via_safety_spec (drop_asserts_prog p6))) fn fn
    (rpostF (eS := via_safety_spec (drop_asserts_prog p6))).
Proof using asm_op_tout rE_trans.
  move=> hmask h6 h8.
  apply: (wiequiv_f_trans_sm (wa2 := withassert_nocontract) (sm2 := total_init)
           (p2 := drop_asserts_prog p6)).
  3: apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total_init)
              (p2 := p6)).
  3: exact: (explicit_init_src_tgt (spp := spp) (wa := withassert_nocontract) (wE := wE)
               (rE := rE) ev erefl hmask asm_op_tout h6).
  3: exact: (drop_asserts_src_tgt (spp := spp) (sm := total_init) (wE := wE) (rE := rE)).
  3: exact: (drop_removable_src_tgt (LC := toec_LoopCounter) (spp := spp) (sm := total_init)
               (wE := wE) (rE := rE) ev h8).
  - by move=> fs1 fs3 /= [_ [fsm hm ->]]; exists fsm.
  by move=> fs1 fs2 fs3 r1 r2 r3 _ _ /= hm ->; exists r2.
Qed.

(* Every run of the source, in the partial mode with its assertions and its
   contracts evaluated, that does not fail is matched by a run of the result
   of the plain extraction through the passes of the extraction for safety,
   in the semantics of EasyCrypt (the mode [total_init], the assertions
   evaluated, the contracts not), that does not fail and computes the same
   results, up to [via_safety_spec]. The masks are fresh in the program that
   [explicit_init] receives. *)
Theorem toec_uprog_via_safety_src_tgt (p p' : uprog) :
  toec_uprog_via_safety fresh_var_ident fresh_removable_ident mask removable p = ok p' ->
  exists p5 p6,
  [/\ toec_uprog_pre_init p = ok p5,
      explicit_init_prog mask p5 = ok p6 &
      mask_ok mask p5 ->
      forall fn,
      wiequiv_f_ withassert withassert_nocontract partial total_init p p' ev ev
        (rpreF (eS := via_safety_spec (drop_asserts_prog p6))) fn fn
        (rpostF (eS := via_safety_spec (drop_asserts_prog p6)))].
Proof using asm_op_tout rE_trans.
  rewrite /toec_uprog_via_safety /toec_uprog_assert /toec_uprog_pre_init.
  t_xrbindP => p6 p1 h1 p2 h2 p3 h3 p5 h5 h6 h8.
  exists p5, p6; split => //.
  - by rewrite h1 /= h2 /= h3.
  move=> hmask fn.
  apply: (wiequiv_f_trans_eq_l (wa2 := withassert_nocontract) (sm2 := total) (p2 := p5)).
  - exact: pre_init_src_tgt h1 h2 h3 h5.
  exact: ei_drop_src_tgt hmask h6 h8.
Qed.

End PROOF.
