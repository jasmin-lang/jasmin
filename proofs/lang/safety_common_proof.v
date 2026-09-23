(* * Semantic lemmas on the assertions of [safety_common.v].

   The safety pass conjoins the assertions it generates with [aands] and
   asserts the conditions of the left values of an instruction before it,
   which [check_xs] licenses. The lemmas below evaluate these assertions in
   any mode; [safe_assertP] relates a sequence of assertions run on one side
   to the empty command on the other. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
Require Import psem safety_common.
Import Utf8.

Lemma read_aands as_ : Sv.Equal (read_eassert (aands as_)) (read_easserts as_).
Proof.
  elim: as_ => //= a l hrec; rewrite read_easserts_cons -hrec => {hrec}.
  case: l.
  + by rewrite /= /read_easserts /=; clear; SvD.fsetdec.
  move=> b l; move: (b::l) => {b} {}l.
  by rewrite read_eassert_Pand.
Qed.

Lemma use_mem_aands as_ : use_mem_eassert (aands as_) = has use_mem_eassert as_.
Proof.
  elim: as_ => //=.
  move=> a [ /= | a' l] hl.
  + by rewrite orbF.
  by move: (a'::l) hl => {a'} {}l <-.
Qed.

Section LEMMAS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

#[local] Existing Instance nosubword.
#[local] Existing Instance withassert.

(* The assertions are evaluated in one mode, which the lemmas below leave
   free; [safe_assertP] needs two of them at once, so the mode is fixed by a
   section of its own. *)
Section MODE.

Context {sm : SemMode}.

(* ------------------------------------------------------------------------- *)
(* Conjunctions of assertions                                                 *)

Lemma aandE gd s a1 a2 :
  sem_eassert gd s (Pand a1 a2) = ok true <->
  sem_eassert gd s a1 = ok true /\ sem_eassert gd s a2 = ok true.
Proof.
  split.
  + rewrite /=; t_xrbindP => b1 h1 b2 h2 /andP [] hb1 hb2; split.
    + by rewrite h1 hb1.
    by rewrite h2 hb2.
  by move=> [] h1 h2; rewrite /= h1 h2.
Qed.

Lemma aandsE_cons gd s a as_ :
  sem_eassert gd s (aands (a::as_)) = ok true <->
  sem_eassert gd s a = ok true /\ sem_eassert gd s (aands as_) = ok true.
Proof.
  case: as_ => /=.
  + by split => [h | []].
  by move=> ??; rewrite aandE.
Qed.

Lemma aandsE_cat gd s as1 as2 :
  sem_eassert gd s (aands (as1 ++ as2)) = ok true <->
  sem_eassert gd s (aands as1) = ok true /\ sem_eassert gd s (aands as2) = ok true.
Proof.
  elim: as1 => /=.
  + by split => [h | []].
  by move=> a as1 hrec; rewrite !aandsE_cons hrec; tauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* The conditions of the left values                                          *)

(* The conditions attached to the left values of an assignment are asserted
   *before* the assignment. [check_xs] checks syntactically that this is
   legitimate; this lemma is what it buys. *)
Lemma check_scaP gd (sc : safety_asserts) s1 s2 okmem W :
  okmem || ~~ has use_mem_eassert sc ->
  disjoint (read_easserts sc) W ->
  evm s1 =[\W] evm s2 ->
  (okmem -> emem s1 = emem s2) ->
  sem_eassert gd s1 (aands sc) = sem_eassert gd s2 (aands sc).
Proof.
  rewrite -read_aands -use_mem_aands.
  move: (aands _) => a hokm /Sv.is_empty_spec hdisj hvm hmem.
  have ? : evm s1 =[read_eassert a] evm s2.
  + by move=> x hx; apply hvm; SvD.fsetdec.
  case: okmem hokm hmem => /=.
  + by move=> _ /(_ erefl) hmem; apply: eq_on_sem_eassert.
  by move=> huse _; apply: use_mem_eassertP_eq_on.
Qed.

End MODE.

(* ------------------------------------------------------------------------- *)
(* Running the generated assertions                                           *)

Section SAFE_ASSERT.

Context {sip : SemInstrParams asm_op syscall_state}.
#[local] Existing Instance progUnit.
#[local] Existing Instance indirect_c.

Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.
Variable (p1 p2 : uprog) (ev : extra_val_t).

Notation gd := (p_globs p1).

(* [safe_assert ii scs] leaves the state untouched and establishes that every
   condition of [scs] holds, while the right-hand side does nothing. The
   conditions are evaluated on the left, under [sm1]. *)
Lemma safe_assertP {sm1 sm2 : SemMode} R spec ii scs :
  wequiv_rec (sm1:=sm1) (sm2:=sm2) p1 p2 ev ev spec R (safe_assert ii scs) [::]
    (fun s1 s2 => R s1 s2 /\ sem_eassert (sm:=sm1) gd s1 (aands scs) = ok true).
Proof.
  apply wkequiv_eq_pred => s1 s2 hR.
  apply wequiv_weaken with (eq_init s1 s2)
    (fun t1 t2 => eq_init s1 s2 t1 t2 /\ sem_eassert (sm:=sm1) gd s1 (aands scs) = ok true).
  - by move=> ?? [].
  - by move=> t1 t2 [[-> ->] h]; split.
  elim: scs => [| sc scs hrec].
  - by apply wequiv_nil => ?? [-> ->]; split.
  rewrite /= -(cats0 [::]) -cat1s.
  rewrite -/(aands (sc :: scs)).
  apply wequiv_cat with
    (fun t1 t2 => eq_init s1 s2 t1 t2 /\ sem_eassert (sm:=sm1) gd s1 sc = ok true).
  - by apply wequiv_assert_left => _ ?? [-> ->] h; split.
  apply wkequiv_eq_pred => t1 t2 [[-> ->] hsc].
  apply wequiv_weaken with (eq_init s1 s2)
    (fun u1 u2 => (u1 = s1 /\ u2 = s2) /\ sem_eassert (sm:=sm1) gd s1 (aands scs) = ok true).
  - by move=> ?? [].
  - move=> u1 u2 [[-> ->] h]; split; first by [].
    by apply/(aandsE_cons (sm := sm1)); split; [exact hsc | exact h].
  exact hrec.
Qed.

End SAFE_ASSERT.

End LEMMAS.
