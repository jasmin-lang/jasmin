(* * Semantic lemmas shared by the users of [safety_common.v]: the [wint_int]
   pass and the safety pass.

   The conditions the two passes generate are built from operators that never
   fail, so the lemmas below hold whatever the mode of the semantics: they are
   stated for an arbitrary [SemMode].  The safety pass evaluates them in the
   total mode, [wint_int] in the partial one. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg eqtype word_ssrZ.
Require Import op_semi psem safety_common.
Import Utf8.

Lemma read_etrue : read_e etrue = Sv.empty.
Proof. done. Qed.

Lemma read_eands es : Sv.Equal (read_e (eands es)) (read_es es).
Proof.
  elim: es => //= e l hrec; rewrite read_es_cons -hrec => {hrec}.
  case: l.
  + rewrite /= read_etrue; SvD.fsetdec.
  move=> a l; move: (a::l) => {a} {}l.
  by rewrite read_e_Papp2.
Qed.

Lemma use_mem_eands es : use_mem (eands es) = has use_mem es.
Proof.
  elim: es => //=.
  move=> a [ /= | a' l] hl.
  + by rewrite orbF.
  by move: (a'::l) hl => {a'} {}l <-.
Qed.

(* Same, one level up: [aands] conjoins a list of assertions. *)
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

Lemma to_val_defined t (x : sem_t t) v : to_val x = v -> is_defined v.
Proof. by move=> /to_valI; case: v. Qed.

(* The conditions are evaluated in one mode, which the lemmas below leave
   free; [safe_assertP] needs two of them at once, so the mode is fixed by a
   section of its own. *)
Section MODE.

Context {sm : SemMode}.

(* ------------------------------------------------------------------------- *)
(* The boolean connectives of the condition language                          *)

Lemma etrueE gd s : sem_cond gd etrue s = ok true.
Proof. done. Qed.

Opaque of_val.

Lemma enotE gd s e b :
  sem_cond gd (enot e) s = ok b <-> sem_cond gd e s = ok (~~ b).
Proof.
  rewrite /sem_cond /= /sem_sop1 /sem_sop1_typed /mk_sem_op /=.
  rewrite /check_safe /= if_same /=; split; t_xrbindP.
  + move=> z z0 he z1 hz1 <- /to_boolI [] <-.
    by rewrite he /= Bool.negb_involutive.
  move=> v he /to_boolI ?; subst v.
  by rewrite he /= (of_val_to_val (t := cbool)) /= Bool.negb_involutive.
Qed.

Lemma eandE gd s e1 e2 :
  sem_cond gd (eand e1 e2) s = ok true <->
    sem_cond gd e1 s = ok true /\ sem_cond gd e2 s = ok true.
Proof.
  rewrite /eand /sem_cond /= /sem_sop2 /sem_sop2_typed /mk_sem_op /=.
  rewrite /check_safe /= if_same /=; split.
  + t_xrbindP => z z0 he1 z1 he2 z2 hz2 z3 hz3 <- /to_boolI [] hand; move: hand.
    case: z2 hz2 => //= hz2; case: z3 hz3 => //= hz3 _.
    by rewrite he1 he2 /=; split; [exact: hz2 | exact: hz3].
  move=> []; t_xrbindP => v -> /to_boolI ?; subst v; move=> v -> /to_boolI ?; subst v.
  by rewrite /= !(of_val_to_val (t := cbool)).
Qed.

Transparent of_val.

Lemma eandsE_nil gd s : sem_cond gd (eands [::]) s = ok true.
Proof. done. Qed.

Lemma eandsE_1 gd s e :
  sem_cond gd (eands [::e]) s = sem_cond gd e s.
Proof. done. Qed.

Lemma eandsE_cons gd s e es :
  sem_cond gd (eands (e::es)) s = ok true <->
  sem_cond gd e s = ok true /\ sem_cond gd (eands es) s = ok true.
Proof.
  rewrite /=; case: es => /=.
  + rewrite etrueE; tauto.
  by move=> ??; rewrite eandE.
Qed.

Opaque eands.

Lemma eandsE_cat gd s es1 es2 :
  sem_cond gd (eands (es1 ++ es2)) s = ok true <->
  sem_cond gd (eands es1) s = ok true /\ sem_cond gd (eands es2) s = ok true.
Proof.
  elim: es1 => //=.
  + by rewrite etrueE; tauto.
  move=> e es1 hrec; rewrite !eandsE_cons hrec; tauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* Same, one level up: the assertions the safety pass generates are
   [safety_asserts], so it reasons through [aands] and [sem_eassert] rather
   than [eands] and [sem_cond].                                              *)

Lemma aandsE_1 gd s a :
  sem_eassert gd s (aands [::a]) = sem_eassert gd s a.
Proof. done. Qed.

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

(* The operator conditions are built as [seq pexpr] and injected into
   [safety_asserts] with [map Pexpr]; this is the bridge between the two
   layers. *)
Lemma aands_map_PexprE gd s l :
  sem_eassert gd s (aands [seq Pexpr e | e <- l]) = ok true <->
  sem_cond gd (eands l) s = ok true.
Proof.
  elim: l => [ | e l hrec]; first by split.
  rewrite /= aandsE_cons eandsE_cons; split.
  + by move=> [] h1 h2; split => //; apply/hrec.
  by move=> [] h1 h2; split => //; apply/hrec.
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
(* The generated conditions, evaluated                                        *)

Section SC.

Context (gd : glob_decls) (s : estate).

Lemma eleiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) ->
  sem_pexpr true gd s e2 = ok (Vint i2) ->
  sem_cond gd (elei e1 e2) s = ok (i1 <=? i2)%Z.
Proof. by rewrite /sem_cond /= => -> ->; case: sm => -[]. Qed.

Lemma eeqiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) ->
  sem_pexpr true gd s e2 = ok (Vint i2) ->
  sem_cond gd (eeqi e1 e2) s = ok (i1 == i2).
Proof. by rewrite /sem_cond /= => -> ->; case: sm => -[]. Qed.

Lemma eneqiP e1 e2 i1 i2 :
  sem_pexpr true gd s e1 = ok (Vint i1) ->
  sem_pexpr true gd s e2 = ok (Vint i2) ->
  sem_cond gd (eneqi e1 e2) s = ok (i1 != i2).
Proof. by rewrite /sem_cond /= => -> ->; case: sm => -[]. Qed.

Lemma sc_sint_rangeP e i sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_sint_range sz e) s = ok true ->
  in_sint_range sz i.
Proof.
  rewrite /sc_sint_range /sc_in_range eandE => he.
  rewrite (eleiP (i1 := wmin_signed sz) _ he) => //.
  by rewrite (eleiP (i2 := wmax_signed sz) he) /in_sint_range => // -[[->] [->]].
Qed.

Lemma sc_uint_rangeP e i sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_uint_range sz e) s = ok true ->
  in_uint_range sz i.
Proof.
  rewrite /sc_uint_range /sc_in_range eandE => he.
  rewrite (eleiP (i1 := 0%Z) _ he) => //.
  by rewrite (eleiP (i2 := wmax_unsigned sz) he) /in_uint_range => // -[[->] [->]].
Qed.

Lemma sc_wi_rangeP e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_wi_range sg sz e) s = ok true ->
  in_wint_range sg sz i = ok tt.
Proof.
  rewrite /sc_wi_range /in_wint_range.
  case: sg => /= he hc.
  + by rewrite (sc_sint_rangeP he hc).
  by rewrite (sc_uint_rangeP he hc).
Qed.

Lemma sc_int_of_word_wrepr e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_wi_range sg sz e) s = ok true ->
  int_of_word sg (wrepr sz i) = i.
Proof.
  move=> he /(sc_wi_rangeP he); rewrite /in_wint_range.
  case: sg => /assertP /andP [] /ZleP ? /ZleP; rewrite /wmax_unsigned => ?.
  + exact: wsigned_repr.
  by apply: wunsigned_repr_small; Lia.lia.
Qed.

Lemma sc_wi_range_of_int e i sg sz :
  sem_pexpr true gd s e = ok (Vint i) ->
  sem_cond gd (sc_wi_range sg sz e) s = ok true ->
  wint_of_int sg sz i = ok (wrepr sz i).
Proof. by move=> he hsc; rewrite /wint_of_int (sc_wi_rangeP he hsc). Qed.

Lemma sem_sc_divmod sz sg (w1 w2 : word sz) e1 e2 :
  sem_pexpr true gd s e1 = ok (Vint (int_of_word sg w1)) ->
  sem_pexpr true gd s e2 = ok (Vint (int_of_word sg w2)) ->
  sem_cond gd (eands (sc_divmod sg sz e1 e2)) s = ok true ->
  ((w2 == 0%R) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == (-1)%R]) = false.
Proof.
  have hz : int_of_word sg (0%R : word sz) = 0%Z.
  + by case: sg => /=; rewrite ?wsigned0 ?wunsigned0.
  move=> h1 h2; rewrite /sc_divmod eandsE_cons.
  rewrite (eneqiP (i2:=0%Z) h2) // => -[[/eqP h0] hsc].
  apply/negbTE/negP => /orP [/eqP ? | /and3P [/eqP ? /eqP hw1 /eqP ?]].
  + by subst w2; apply: (h0 hz).
  subst w2 sg; move: hsc => /=; rewrite eandsE_1 enotE.
  have -> // : sem_cond gd (eand (eeqi e1 (emin_signed sz)) (eeqi e2 (Pconst (-1)))) s = ok true.
  by rewrite eandE (eeqiP (i2:= wmin_signed sz) h1) // (eeqiP (i2:= -1) h2) //
     -hw1 eqxx /= wsignedN1 eqxx.
Qed.

(* In the total mode a successful evaluation returns a defined value, so the
   type of that value determines its shape. *)
Lemma sem_pexpr_tovI e v t :
  sem_pexpr (sm := total) true gd s e = ok v ->
  type_of_val v = t ->
  match t with
  | cbool => exists b : bool, v = b
  | cint => exists i : Z, v = i
  | carr len => exists a : WArray.array len, v = Varr a
  | cword ws => exists w : word ws, v = Vword w
  end.
Proof.
  move=> /sem_pexpr_defined hd /type_of_valI h.
  by case: t h hd => // [||ws] [-> | ].
Qed.

End SC.

(* The conditions attached to the left values of an assignment are asserted
   *before* the assignment.  [check_xs] checks syntactically that this is
   legitimate; these two lemmas are what it buys. *)

Lemma check_scP gd (sc : seq pexpr) s1 s2 okmem W :
  okmem || ~~ has use_mem sc ->
  disjoint (read_es sc) W ->
  evm s1 =[\W] evm s2 ->
  (okmem -> emem s1 = emem s2) ->
  sem_cond gd (eands sc) s1 = sem_cond gd (eands sc) s2.
Proof.
  rewrite -read_eands -use_mem_eands /sem_cond.
  move: (eands _) => e hokm /Sv.is_empty_spec hdisj hvm hmem.
  suff : [elaborate sem_pexpr true gd s1 e = sem_pexpr true gd s2 e].
  + by move=> ->.
  have ? : evm s1 =[read_e e] evm s2.
  + by move=> x hx; apply hvm; SvD.fsetdec.
  case: okmem hokm hmem => /=.
  + by move=> _ /(_ erefl) hmem; apply: (eq_on_sem_pexpr true gd hmem).
  by move=> huse _; apply use_memP_eq_on.
Qed.

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
   condition of [scs] holds, while the right-hand side does nothing.  This is
   the first place where the two modes really differ: the conditions are
   evaluated on the left, under [sm1]. *)
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

(* The unit syscall semantics does not touch the memory and returns values of
   the declared output types. *)
Lemma syscall_u_toutP o fs fs2 :
  fexec_syscall o fs = ok fs2 ->
  fmem fs = fmem fs2 /\
  List.map type_of_val fs2.(fvals) = map eval_atype (scs_tout (syscall_sig_u o)).
Proof.
  rewrite /fexec_syscall.
  t_xrbindP => -[[scs m_] vs_] + [<-] /=.
  case: o => ws len /=; rewrite /exec_getrandom_u.
  t_xrbindP => a ha t ht heq.
  by move=> <- /= _ <- <-.
Qed.

End SAFE_ASSERT.

End LEMMAS.
