(* * Correctness of the extraction for safety ([toec_uprog_safety]).

   The semantics of the extracted program is that of EasyCrypt: the mode
   [total_init] (every access succeeds and every output of an instruction is
   defined), the assertions evaluated, the contracts not
   ([withassert_nocontract]). The semantics of the source is the partial
   mode, with the assertions and the contracts evaluated ([withassert]).

   - [common_tgt_src]: every run of the result of the passes common to both
     extractions ([toec_uprog_common]) that does not fail corresponds to a
     run of the source that does not fail, with related arguments and results
     ([common_rel]): equal, or, when [wi2i_prog] runs, the words annotated
     [wint] read as integers.
   - [toec_uprog_safety_tgt_src]: every run of the result of the extraction
     for safety that does not fail corresponds to a run of the source that
     does not fail, with related arguments and results ([safety_wi_pre],
     [safety_wi_post]).

   Both compose the correctness of each pass. The well-typedness that
   [dead_args] needs ([total_ok]) holds on the program it receives, which the
   chain type checks ([check_prog_total_ok]). *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import wint_int toec_for toec_while normalize_calls contracts_to_asserts safety
  explicit_init simplify_asserts assert_facts typing_check dead_code dead_args toec_prog.
Require Import wint_int_proof normalize_calls_proof contracts_to_asserts_proof safety_proof
  toec_while_proof toec_for_proof explicit_init_proof simplify_asserts_proof
  assert_facts_proof typing_check_proof dead_code_total_proof dead_args_proof.

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

Context
  (fresh_var_ident fresh_copy_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Context (get_info : _uprog -> Sv.t * (var -> option (signedness * var))).
Context (ev : extra_val_t).

(* The relation between the arguments, or the results, of a run of the result
   of [toec_uprog_common] and those of a run of its source: equal, or, when
   [wi2i_prog] runs, related by [R] ([vs_pre], [vs_post]). *)
Definition common_rel (wi2i : bool) (R : values -> values -> Prop) : fstate -> fstate -> Prop :=
  if wi2i then fs_rel R else eq.

(* Every run of the result of [toec_uprog_common], in the partial mode with
   the assertions and the contracts evaluated, that does not fail corresponds
   to a run of the source, in the same mode, that does not fail, with
   arguments and results related by [common_rel]. *)
Lemma common_tgt_src (wi2i : bool) (p pc : uprog) :
  toec_uprog_common fresh_var_ident get_info wi2i p = ok pc ->
  forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
  let fsig := (build_sig (get_info p).2 (fn, fd)).2 in
  wiequiv_f_ withassert withassert partial partial pc p ev ev
    (fun _ _ => common_rel wi2i (vs_pre fsig.1)) fn fn
    (fun _ _ _ _ => common_rel wi2i (vs_post fsig.2)).
Proof using rE_trans.
  move=> + fn fd hfd fsig; rewrite /toec_uprog_common; t_xrbindP => pi hpi pn hpn hpc.
  have hc : wiequiv_f_ withassert withassert partial partial pc pi ev ev
      (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
  - apply: (wiequiv_f_trans_eq_r (wa2 := withassert) (sm2 := partial)
             (p2 := toec_while_prog pn)).
    + exact: (toec_for_l (rE := rE) ev hpc).
    apply: (wiequiv_f_trans_eq_r (wa2 := withassert) (sm2 := partial) (p2 := pn)).
    + exact: (toec_while_l (rE := rE) pn ev).
    exact: (normalize_calls_l (rE := rE) ev hpn).
  case: wi2i hpi => hpi /=.
  - apply: wkequiv_io_trans hc (wi2w_callP ev hpi hfd).
    + by move=> fs1 fs3 h; exists fs1.
    by move=> > _ _ [fr2 ->].
  case: hpi => ?; subst pi.
  by apply: wkequiv_io_weaken hc.
Qed.

(* From the output of [sc_prog], in the total mode and with the assertions
   evaluated, to the result of [toec_uprog_common], in the partial mode and
   with the assertions and the contracts evaluated. *)
Lemma sc_front_tgt_src (pc p2 p3 : uprog) fn :
  contracts_to_asserts_prog fresh_copy_ident pc = ok p2 ->
  sc_prog p2 = ok p3 ->
  wiequiv_f_ withassert_nocontract withassert total partial p3 pc ev ev
    (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using rE_trans.
  move=> h2 h3.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := partial) (p2 := p2)).
  - exact: (safety_callP (spp := spp) (wa := withassert_nocontract) (rE := rE) erefl ev h3).
  exact: (contracts_to_asserts_tgt_src (sm := partial) (rE := rE) ev h2).
Qed.

Context (mask : var -> var).

(* From the output of [explicit_init], in the mode [total_init], to the output
   of [sc_prog], in the total mode, both with the assertions evaluated:
   [toec_while] runs in between. *)
Lemma ei_tgt_src (p3 p6 : uprog) fn :
  explicit_init_prog mask (toec_while_prog p3) = ok p6 ->
  wiequiv_f_ withassert_nocontract withassert_nocontract total_init total p6 p3 ev ev
    (rpreF (eS := mask_spec)) fn fn (rpostF (eS := mask_spec)).
Proof using rE_trans.
  move=> h6.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total)
           (p2 := toec_while_prog p3)).
  - exact: (explicit_init_callP (wa := withassert_nocontract) erefl ev h6).
  exact: (toec_while_l (wa := withassert_nocontract) (sm := total) (rE := rE) p3 ev).
Qed.

Context (protect : funname -> var -> bool).
Context (dead_info : (funname -> var -> bool) -> _uprog ->
                     funname -> option (seq bool) * option (seq bool)).


(* From the output of [dead_args] to the output of [explicit_init], both in
   the mode [total_init] with the assertions evaluated. *)
Lemma dead_tgt_src {LC : LoopCounter} (p6 p9 : uprog) info fn :
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  check_prog p8 = ok tt ->
  dead_args_info protect (dead_info protect) p8 = ok (p9, info) ->
  wiequiv_f_ withassert_nocontract withassert_nocontract total_init total_init p9 p6 ev ev
    (rpreF (eS := dead_args_tgt_src_spec info p8)) fn fn
    (rpostF (eS := dead_args_tgt_src_spec info p8)).
Proof using rE_trans.
  move=> p8 /check_prog_total_ok hok h9.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total_init) (p2 := p8)).
  - exact: (dead_args_tgt_src (rE := rE) ev hok h9).
  apply: (wiequiv_f_trans_eq_l (wa2 := withassert_nocontract) (sm2 := total_init)
           (p2 := simplify_asserts_prog p6)).
  - exact: (assert_facts_tgt_src (rE := rE)).
  exact: (simplify_asserts_tgt_src (rE := rE)).
Qed.

(* The relation between a run of the result of the extraction for safety and a
   run of the result of [toec_uprog_common]: the arguments given to the latter are
   those given to the former, plus the removed ones, once the masks that
   [explicit_init] adds after the arrays are dropped; the masks describe the
   initialisation of the arrays and the scalars are defined; the arguments
   have the types of the parameters of [p8], the input of [dead_args]. The
   results are related in the same way. *)
Definition safety_spec (info : keep_info) (p8 : uprog) : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs' fs =>
       fn1 = fn2 /\
       exists2 fsm, mask_fs fsm fs &
         fs' = fs_keep (kparams info fn1) fsm /\
         forall fd, get_fundef (p_funcs p8) fn1 = Some fd ->
           is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fsm))
   ; rpostF_ := fun fn1 _ _ _ fr' fr =>
       exists2 frm, mask_fs frm fr & fr' = fs_keep (kres info fn1) frm |}.

Lemma safety_chain_tgt_src {LC : LoopCounter} (pc p2 p3 p6 p9 : uprog) info fn :
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  contracts_to_asserts_prog fresh_copy_ident pc = ok p2 ->
  sc_prog p2 = ok p3 ->
  explicit_init_prog mask (toec_while_prog p3) = ok p6 ->
  check_prog p8 = ok tt ->
  dead_args_info protect (dead_info protect) p8 = ok (p9, info) ->
  wiequiv_f_ withassert_nocontract withassert total_init partial p9 pc ev ev
    (rpreF (eS := safety_spec info p8)) fn fn (rpostF (eS := safety_spec info p8)).
Proof using rE_trans.
  move=> p8 h2 h3 h6 hok h9.
  apply: (wiequiv_f_trans_eq_r (wa2 := withassert_nocontract) (sm2 := total) (p2 := p3));
    last first.
  - exact: sc_front_tgt_src h2 h3.
  apply: (wiequiv_f_trans_sm (wa2 := withassert_nocontract) (sm2 := total_init) (p2 := p6)).
  3: exact: dead_tgt_src hok h9.
  3: exact: ei_tgt_src h6.
  - move=> fs1 fs3 /= [_ [fsm hm [-> hty]]]; exists fsm => //.
  by move=> fs1 fs2 fs3 r1 r2 r3 _ _ /= -> hm; exists r2.
Qed.

(* The program that [explicit_init] receives in [toec_uprog_safety]. *)
Definition toec_uprog_pre_init (wi2i : bool) (p : _uprog) : cexec _uprog :=
  Let p := toec_uprog_common fresh_var_ident get_info wi2i p in
  Let p := contracts_to_asserts_prog fresh_copy_ident p in
  Let p := sc_prog p in
  ok (toec_while_prog (pT := progUnit) p).

(* The relation between a run of the result of the extraction for safety and
   a run of its source [p], through a run of the result of
   [toec_uprog_common], related to the former by [safety_spec] and to the
   latter by [common_rel] ([vs_pre], [vs_post] of the signature [fsig] of the
   function in [p]). *)
Definition safety_wi_pre (wi2i : bool) (info : keep_info) (p8 : uprog)
    (fsig : seq (extended_type Z) * seq (extended_type Z))
    (fn1 fn2 : funname) (fs' fs : fstate) : Prop :=
  exists2 fsi, rpreF (eS := safety_spec info p8) fn1 fn2 fs' fsi &
    common_rel wi2i (vs_pre fsig.1) fsi fs.

Definition safety_wi_post (wi2i : bool) (info : keep_info) (p8 : uprog)
    (fsig : seq (extended_type Z) * seq (extended_type Z))
    (fn1 fn2 : funname) (fs' fs fr' fr : fstate) : Prop :=
  exists fsi fri,
    [/\ rpreF (eS := safety_spec info p8) fn1 fn2 fs' fsi,
        common_rel wi2i (vs_pre fsig.1) fsi fs,
        rpostF (eS := safety_spec info p8) fn1 fn2 fs' fsi fr' fri &
        common_rel wi2i (vs_post fsig.2) fri fr].

(* Every run of the result of the extraction for safety, in the semantics of
   EasyCrypt (the mode [total_init], the assertions evaluated, the contracts
   not), that does not fail corresponds to a run of the source, in the
   partial mode with its assertions and its contracts evaluated, that does
   not fail and computes the same results, up to [safety_wi_pre] and
   [safety_wi_post]. *)
Theorem toec_uprog_safety_tgt_src (wi2i : bool) (p p' : uprog) :
  toec_uprog_safety fresh_var_ident get_info fresh_copy_ident wi2i mask protect dead_info p
    = ok p' ->
  exists p5 p6 info,
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  [/\ toec_uprog_pre_init wi2i p = ok p5,
      explicit_init_prog mask p5 = ok p6,
      dead_args_info (LC := toec_LoopCounter) protect (dead_info protect) p8 = ok (p', info) &
      forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
      let fsig := (build_sig (get_info p).2 (fn, fd)).2 in
      wiequiv_f_ withassert_nocontract withassert total_init partial p' p ev ev
        (safety_wi_pre wi2i info p8 fsig) fn fn (safety_wi_post wi2i info p8 fsig)].
Proof using rE_trans.
  rewrite /toec_uprog_safety /dead_args_prog /toec_uprog_pre_init.
  t_xrbindP => pc hpc p2 h2 p3 h3 p6 h6 hok r h9 <-.
  case: r h9 => p9 info h9; exists (toec_while_prog p3), p6, info; split => //.
  - by rewrite hpc /= h2 /= h3.
  move=> fn fd hfd.
  apply: wkequiv_io_trans (safety_chain_tgt_src h2 h3 h6 hok h9)
                          (common_tgt_src hpc hfd).
  - by move=> fs' fs [fsi h12 h23]; exists fsi.
  by move=> fs' fsi fs fr' fr h12 h23 [fri hq12 hq23]; exists fsi, fri.
Qed.

End PROOF.

(* * The plain extraction ([toec_uprog]) under the safety of the extraction
   for safety. *)

From ITree Require Import Rutt.
Require Import drop_asserts drop_asserts_proof.

Section EQUIV.

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
  {rE_trans : EventRels_trans rE rE rE}
  {rE_ans : EventRels_ans_total rE}
  {rE_flip : EventRels_trans (EventRels_flip rE) rE rE}.

Notation wiequiv_f_ wa1 wa2 sm1 sm2 :=
  (wiequiv_f (wa1 := wa1) (wa2 := wa2) (sm1 := sm1) (sm2 := sm2)).
Notation safe_f_ wa sm := (safe_f (wa := wa) (sm := sm) (wE := wE)).

Context
  (fresh_var_ident fresh_copy_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Context (get_info : _uprog -> Sv.t * (var -> option (signedness * var))).
Context (ev : extra_val_t).
Context (mask : var -> var).
Context (protect : funname -> var -> bool).
Context (dead_info : (funname -> var -> bool) -> _uprog ->
                     funname -> option (seq bool) * option (seq bool)).

(* The safety of the result of the extraction for safety, in the semantics of
   EasyCrypt, on the arguments that satisfy [P], gives the safety of the
   result of [toec_uprog_common] and of the source, both in the partial mode
   with the assertions and the contracts evaluated, on the related
   arguments. *)
Lemma toec_uprog_safety_safe (wi2i : bool) (p pc ps : uprog) :
  toec_uprog_common fresh_var_ident get_info wi2i p = ok pc ->
  toec_uprog_safety fresh_var_ident get_info fresh_copy_ident wi2i mask protect dead_info p
    = ok ps ->
  exists p5 p6 info,
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  [/\ toec_uprog_pre_init fresh_var_ident fresh_copy_ident get_info wi2i p = ok p5,
      explicit_init_prog mask p5 = ok p6,
      dead_args_info (LC := toec_LoopCounter) protect (dead_info protect) p8 = ok (ps, info) &
      forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
      let fsig := (build_sig (get_info p).2 (fn, fd)).2 in
      forall P, safe_f_ withassert_nocontract total_init P ps ev fn ->
      safe_f_ withassert partial
        (fun fsi => exists fss, rpreF (eS := safety_spec info p8) fn fn fss fsi /\ P fss)
        pc ev fn /\
      safe_f_ withassert partial
        (fun fs => exists fss, safety_wi_pre wi2i info p8 fsig fn fn fss fs /\ P fss)
        p ev fn].
Proof using rE_ans rE_trans.
  move=> hpc; rewrite /toec_uprog_safety /dead_args_prog /toec_uprog_pre_init hpc /=.
  t_xrbindP => p2 h2 p3 h3 p6 h6 hok r h9 <-.
  case: r h9 => p9 info h9; exists (toec_while_prog p3), p6, info; split => //.
  - by rewrite h2 /= h3.
  move=> fn fd hfd P hsafe.
  have hspc := wiequiv_f_safe_f (safety_chain_tgt_src (rE := rE) ev (fn := fn) h2 h3 h6 hok h9) hsafe.
  split; first exact: hspc.
  move=> fs [fss [[fsi hss hc] hP]].
  apply: (wiequiv_f_safe_f (common_tgt_src (rE := rE) ev hpc hfd) (hspc _ _)).
  by exists fsi; split => //; exists fss.
Qed.

(* The plain extraction [p'] and its source [p] are equivalent on the
   arguments on which the extraction for safety [ps] is safe. Let [P] be
   arguments of [ps] on which [ps] does not fail in the semantics of
   EasyCrypt (the safety proved in EasyCrypt). Take an argument [fs'] of
   [p'], related by [safety_spec] to an argument of [ps] in [P], and related
   by [common_rel] to an argument [fs] of [p]. The run of [p'] on [fs'], in
   the semantics of EasyCrypt, does not fail, and it is equivalent to the run
   of [p] on [fs], in the partial mode with the assertions and the contracts
   evaluated: same events, results related by [common_rel]. The relation
   holds in both directions. So a property of [p'] proved in EasyCrypt,
   together with the safety of [ps], gives the same property of [p]. *)
Theorem toec_uprog_equiv (wi2i : bool) (p ps p' : uprog) :
  toec_uprog_safety fresh_var_ident get_info fresh_copy_ident wi2i mask protect dead_info p
    = ok ps ->
  toec_uprog fresh_var_ident get_info wi2i p = ok p' ->
  exists p5 p6 info,
  let p8 := assert_facts_prog (simplify_asserts_prog p6) in
  [/\ toec_uprog_pre_init fresh_var_ident fresh_copy_ident get_info wi2i p = ok p5,
      explicit_init_prog mask p5 = ok p6,
      dead_args_info (LC := toec_LoopCounter) protect (dead_info protect) p8 = ok (ps, info) &
      forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
      let fsig := (build_sig (get_info p).2 (fn, fd)).2 in
      forall P, safe_f_ withassert_nocontract total_init P ps ev fn ->
      let pre fs' fs :=
        common_rel wi2i (vs_pre fsig.1) fs' fs /\
        exists fss, rpreF (eS := safety_spec info p8) fn fn fss fs' /\ P fss in
      let post := common_rel wi2i (vs_post fsig.2) in
      [/\ wiequiv_f_ withassert_nocontract withassert total_init partial p' p ev ev
            (fun _ _ => pre) fn fn (fun _ _ _ _ => post),
          wiequiv_f (wa1 := withassert) (wa2 := withassert_nocontract) (sm1 := partial)
            (sm2 := total_init) (rE0 := EventRels_flip rE) p p' ev ev
            (fun _ _ fs fs' => pre fs' fs) fn fn (fun _ _ _ _ fr fr' => post fr' fr) &
          forall fs' fs, pre fs' fs ->
          rutt (EPreRel (rE0 := rE)) (EPostRel (rE0 := rE)) post
            (isem_fun (wa := withassert_nocontract) (sm := total_init) p' ev fn fs')
            (isem_fun (wa := withassert) (sm := partial) p ev fn fs)]].
Proof using rE_ans rE_flip rE_trans.
  rewrite /toec_uprog; t_xrbindP => hps pc hpc <-.
  have [p5 [p6 [info [h5 h6 h9 hs]]]] := toec_uprog_safety_safe hpc hps.
  exists p5, p6, info; split => // fn fd hfd P hsafe.
  have [hspc _] := hs fn fd hfd P hsafe.
  have hflip := wiequiv_f_flip_safe (erase_src_tgt (rE := rE) pc ev (fn := fn)) hspc.
  have hsp' := wiequiv_f_safe_f (erase_src_tgt (rE := rE) pc ev (fn := fn)) hspc.
  set pre := fun fs' fs => common_rel wi2i _ fs' fs /\ _.
  set post := common_rel wi2i (vs_post _).
  have h1 : wiequiv_f_ withassert_nocontract withassert total_init partial
      (drop_asserts_prog pc) p ev ev (fun _ _ => pre) fn fn (fun _ _ _ _ => post).
  - apply: (wkequiv_io_trans (rE12 := EventRels_flip rE) (rE23 := rE) _ _ (hflip _ _)
             (common_tgt_src (rE := rE) ev hpc hfd)).
    + by move=> fs' fs [hc hP]; exists fs'.
    by move=> > _ _ [r /= ->].
  split => //.
  - apply: (wkequiv_io_weaken _ _ _ _ (wiequiv_f_flip_safe h1 (hsp' _ _))) => //.
    by move=> fs fs' [hc hP]; split => //; exists fs'.
  move=> fs' fs hpre; apply: (wiequiv_f_safe_rutt h1 hpre _).1.
  by apply: (hsp' _ _); exists fs'; case: hpre.
Qed.

End EQUIV.
