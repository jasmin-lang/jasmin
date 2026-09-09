From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import psem compiler_util.
Require Import allocation allocation_proof.
Require Import remove_assert.
Require Export legalize_names.
Import Utf8 ssrfun.

(* [legalize_names_prog] first strips assertions ([remove_assert_prog])
   before renaming, because the allocation checker below has no case for
   [Cassert] and would reject any program still containing one (see
   [check_i] in [allocation.v]: its final wildcard case
   [| _, _ => Error (alloc_error "instructions not equals")] covers
   [Cassert] on either side).

   [proofs/compiler/remove_assert_proof.v]'s own [it_remove_assert_progP]
   is *not* directly reusable here: it is stated at
   [(wa1 := withassert) (wa2 := noassert)] (the genuine with-asserts to
   without-asserts semantic transition used by the main compiler
   pipeline), whereas every program in the toEC pipeline -- including
   this pass's own input [p] -- is, by the time it reaches here, already
   interpreted under the single ambient [WithAssert] instance
   ([noassert], the only one globally registered, see
   [proofs/lang/sem_params.v]) on *both* sides (confirmed directly via
   [Set Printing All] on this file's own [legalize_names_proof]
   statement). [wiequiv_f]'s [wa1]/[wa2] are ordinary (non-typeclass-tied)
   arguments to the *value* [p]/[p'] -- crossing from [withassert] to
   [noassert] and staying at [noassert] throughout are different
   propositions, so [it_remove_assert_progP]'s conclusion cannot be
   transported to the [noassert]/[noassert] case needed here.

   The proof below is nonetheless the *exact* structural clone of
   [it_remove_assert_progP]'s proof script (same [Checker_e]/[Pi]/[Pc]
   induction), only with [wa1] left at its default [noassert] instead of
   pinned to [withassert]: none of that script actually depends on which
   value [wa1] takes -- in particular the one case that mentions
   [WithAssert] at all ([wequiv_assert_left]'s use in the [Cassert] case)
   discharges its [assert_allowed -> ...] hypothesis by exhibiting the
   SAME relation ([st_eq]) on both sides of the implication, which holds
   regardless of [assert_allowed]'s value; under [noassert] specifically
   it would in fact also be dischargeable vacuously ([assert_allowed] is
   [false]), but the stronger [st_eq]-preservation argument works
   uniformly for either value, hence needs no adjustment. *)
Section REMOVE_ASSERT_NOASSERT.

  Context
    {wsw : WithSubWord}
    {dc : DirectCall}
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    {pT : progT} {sCP : semCallParams}.

  Context (q q' : prog) (ev : extra_val_t).

  Hypothesis remove_assert_ok : remove_assert_prog q = q'.

  Lemma eq_q_extra : p_extra q' = p_extra q.
  Proof using remove_assert_ok. by rewrite -remove_assert_ok. Qed.

  Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  #[local] Notation st_eq := (st_rel (λ _ : unit, eq) tt).

  Lemma st_rel_eq d s1 s2 : st_rel (λ _ : unit, eq) d s1 s2 -> s1 = s2.
  Proof. by case: s1 s2 => ??? [] ??? [] /= <- <- <-. Qed.

  Program Instance checker_ra_eq_na : Checker_e (st_rel (λ _ : unit, eq)) :=
    {| relational_logic.check_es _ x y _ := x = y;
       relational_logic.check_lvals _ x y _ := x = y; |}.

  Instance checker_ra_eqP_na : Checker_eq q q' checker_ra_eq_na.
  Proof using remove_assert_ok.
    rewrite -remove_assert_ok.
    constructor.
    - by move => > /wdb_ok_eq <- <- > /st_rel_eq <-; eauto.
    by move => > /wdb_ok_eq <- <- > /st_rel_eq <- -> /=; eexists; first reflexivity.
  Qed.
  #[local] Hint Resolve checker_ra_eqP_na : core.

  Let Pi (i : instr) :=
      wequiv_rec q q' ev ev eq_spec st_eq [:: i] (remove_assert_i i) st_eq.

  Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

  Let Pc (c : cmd) :=
      wequiv_rec q q' ev ev eq_spec st_eq c (remove_assert_c remove_assert_i c) st_eq.

  Lemma it_remove_assert_prog_noassertP fn :
    wiequiv_f q q' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
  Proof using remove_assert_ok.
    apply wequiv_fun_ind_wa => {fn}.
    move=> fn _ fs ft [<- <-] fd hget.
    rewrite -{1 2}remove_assert_ok get_map_prog hget /=.
    eexists; first reflexivity.
    move=> _; split => //.
    move=> s1 hinit; exists s1 => //=.
    + by apply: eq_initialize hinit => //; rewrite eq_q_extra.
    exists st_eq, st_eq; split => //; cycle -1.
    + by move => ? _ fr /st_rel_eq <- hfin; exists fr.
    move: (f_body fd) => {hget hinit s1 fs ft fn fd}.
    apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
    + by apply wequiv_nil.
    + by move=> i c hi hc; rewrite -cat1s; apply wequiv_cat with st_eq.
    + by move => >; apply wequiv_assgn_rel_eq with checker_ra_eq_na tt.
    + by move => >; apply wequiv_opn_rel_eq with checker_ra_eq_na tt.
    + move => >; apply wequiv_syscall_rel_eq_core with checker_ra_eq_na tt => //.
      by move => > <- ->; eauto.
    + by move => >; apply wequiv_assert_left.
    + move=> > hc1 hc2 ii.
      by apply wequiv_if_rel_eq with checker_ra_eq_na tt tt tt.
    + move=> > hc >.
      by apply wequiv_for_rel_eq with checker_ra_eq_na tt tt.
    + move=> > hc hc' >.
      by apply wequiv_while_rel_eq with checker_ra_eq_na tt.
    move=> >.
    apply wequiv_call_rel_eq_wa with checker_ra_eq_na tt => //.
    move=> ?? <-; exact/wequiv_fun_rec.
  Qed.

End REMOVE_ASSERT_NOASSERT.

Section LEGALIZE_NAMES_PROOF.

Context
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
  {rE0_trans : EventRels_trans rE0 rE0 rE0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.

Context
  (rename : funname -> var -> Ident.ident)
  (p p' : uprog)
  (ev : extra_val_t)
  (legalize_names_ok : legalize_names_prog rename p = ok p')
.

Lemma legalize_names_proof fn :
  wiequiv_f p p' ev ev
    (rpreF (eS := uincl_spec)) fn fn (rpostF (eS := uincl_spec)).
Proof using legalize_names_ok rE0_trans.
move: legalize_names_ok; rewrite /legalize_names_prog /=.
t_xrbindP => hcheck heq.
rewrite -heq.
have step1 :=
  it_remove_assert_prog_noassertP
    (wsw := nosubword) (dc := dc) (ep := ep) (spp := spp) (sCP := sCP_unit)
    (E := E) (E0 := E0) (wE := wE) (rE := rE0)
    (q := p) (q' := remove_assert_prog p) ev (erefl _) (fn := fn).
have step2 :=
  it_alloc_call_uprogP
    (wsw := nosubword) (dc := dc) (ep := ep) (spp := spp) (sip := sip)
    (LC := legalize_names_LC)
    (E := E) (E0 := E0) (wE := wE) (rE := rE0)
    (dead_vars_fd := legalize_names_dead_vars)
    ev (p_globs p) hcheck (fn := fn).
move: step1 step2; apply wiequiv_f_trans => //.
+ by move=> fs1 fs3 h; exists fs1.
by move=> fs1 fs2 fs3 r1 r3 _ _ [r2 -> h].
Qed.

End LEGALIZE_NAMES_PROOF.
