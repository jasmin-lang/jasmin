From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem.

Section test.

Context {asm_op syscall_state} {spp : SemPexprParams asm_op syscall_state}.

(* n is non-positive and increasing *)
Definition clear_loop ws p n :=
  let ir1 :=
    Cassgn (Lmem ws p (Pvar (mk_lvar n))) AT_keep (sword ws) (pword_of_int ws 0) in
  let ir2 :=
    Cassgn (Lvar n) AT_keep (sword Uptr) (Papp2 (Oadd (Op_w Uptr)) (Pvar (mk_lvar n)) (pword_of_int Uptr (wsize_size ws))) in
  let body :=
    map (MkI dummy_instr_info) [:: ir1; ir2] in
  let ir := Cwhile NoAlign [::] (Papp2 (Ole (Cmp_w Signed Uptr)) (Pvar (mk_lvar n)) (pword_of_int Uptr 0)) body in
  let i := MkI dummy_instr_info ir in
  i.

(* n is non-negative and decreasing *)
Definition clear_loop_positive ws p n :=
  let ir1 :=
    Cassgn (Lmem ws p (Pvar (mk_lvar n))) AT_keep (sword ws) (pword_of_int ws 0) in
  let ir2 :=
    Cassgn (Lvar n) AT_keep (sword Uptr) (Papp2 (Osub (Op_w Uptr)) (Pvar (mk_lvar n)) (pword_of_int Uptr (wsize_size ws))) in
  let body :=
    map (MkI dummy_instr_info) [:: ir1; ir2] in
  let ir := Cwhile NoAlign [::] (Papp2 (Ole (Cmp_w Signed Uptr)) (pword_of_int Uptr 0) (Pvar (mk_lvar n))) body in
  let i := MkI dummy_instr_info ir in
  i.

Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Lemma mod_small_neg a b : (- b <= a < 0)%Z -> (a mod b)%Z = (b + a)%Z.
Proof.
  move=> hle.
  apply sym_equal.
  by apply (Z.mod_unique _ _ (-1)); Lia.lia.
Qed.

Lemma modulus_m' n1 n2 : (n1 <= n2)%coq_nat ->
  (word.modulus n1 <= word.modulus n2)%Z.
Proof.
  move=> hle.
  rewrite /word.modulus !two_power_nat_equiv.
  apply: Z.pow_le_mono_r; first by [].
  Lia.lia.
Qed.

(* TODO: probably, there is a cleaner proof *)
Lemma wsigned_sub sz p n :
  (wmin_signed sz <= wsigned p - n <= wmax_signed sz)%Z ->
  wsigned (p - wrepr sz n) = (wsigned p - n)%Z.
Proof.
  move=> h.
  rewrite -{1}(wrepr_signed p).
  rewrite -wrepr_sub.
  rewrite wsignedE. rewrite wunsigned_repr.
  case heq: msb => //.
  + move: heq; rewrite msb_wordE word.msbE /=.
    have: (wmin_signed sz <= wsigned p - n < 0 \/ 0 <= wsigned p - n <= wmax_signed sz)%Z.
    + by Lia.lia.
    case=> hle.
    + rewrite mod_small_neg.
      + rewrite -/(wbase _). Lia.lia.
      rewrite /wmin_signed in hle.
      have := modulus_m' _ _ (Nat.le_succ_diag_r (wsize_size_minus_1 sz)). Lia.lia.
    rewrite Z.mod_small.
    + move=> /ssrZ.lezP. rewrite /wmax_signed in hle. Lia.lia.
    rewrite /wmax_signed in hle.
    have := modulus_m' _ _ (Nat.le_succ_diag_r (wsize_size_minus_1 sz)). Lia.lia.
  move: heq; rewrite msb_wordE word.msbE /=.
  have: (wmin_signed sz <= wsigned p - n < 0 \/ 0 <= wsigned p - n <= wmax_signed sz)%Z.
  + by Lia.lia.
  case=> hle.
  + rewrite mod_small_neg.
    + move=> /ssrZ.lezP.
      rewrite /word.modulus two_power_nat_S -/(word.modulus _).
      rewrite /wmin_signed in hle.
      Lia.lia.
    rewrite /wmin_signed in hle.
    have := modulus_m' _ _ (Nat.le_succ_diag_r (wsize_size_minus_1 sz)). Lia.lia.
  rewrite Z.mod_small //.
  rewrite /wmax_signed in hle.
  have := modulus_m' _ _ (Nat.le_succ_diag_r (wsize_size_minus_1 sz)). Lia.lia.
Qed.

Lemma wsize_size_wmin_signed s : (wmin_signed U8 < - wsize_size s)%Z.
Proof. by case: s. Qed.

Lemma wmin_signed_m (s s' : wsize) : (s ≤ s')%CMP -> (wmin_signed s' <= wmin_signed s)%Z.
Proof.
  move=> hle.
  rewrite /wmin_signed.
  apply -> Z.opp_le_mono. apply modulus_m'.
  apply wsize_size_m. assumption.
Qed.

(* We use an ind principle tailored to our needs: in the inductive case, we want to consider
  only non-negative [x] but we want to allow the induction hypothesis to use negative [y].
  This is true because we request on top of that that [P] holds on all negative ints.
*)
Lemma Z_better_ind : forall P : Z -> Prop,
(forall x : Z, (x < 0)%Z -> P x) ->
(forall x : Z, (forall y : Z, (y < x)%Z -> P y) -> (0 <= x)%Z -> P x) ->
forall x : Z, P x.
Proof.
  intros Q Hneg Hpos x.
  destruct (Z.le_gt_cases 0 x); last first.
  + by apply Hneg.
  revert x H.
  apply Zlt_0_ind.
  intros. apply Hpos => //. intros.
  destruct (Z.le_gt_cases 0 y).
  + apply H. done.
  apply Hneg. done.
Qed.

Lemma clear_loop_positive_spec : forall ws (p n:var_i) s1 s2 (w wp : word Uptr),
  p.(v_var) <> n.(v_var) ->
  get_var s1.(evm) n = ok (Vword w) ->
  get_var s1.(evm) p = ok (Vword wp) ->
  sem_I P ev s1 (clear_loop_positive ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ sv_of_list v_var [::n;p] ].
Proof.
  move=> ws p n s1 s2 w wp hneq hgetn hgetp.
  (* the administrative stuff is painful and ugly *)
  move: w {2}(wsigned w) (refl_equal (wsigned w)) s1 hgetn hgetp => w N; move: N w.
  apply: Z_better_ind => [N hlt|N ih hle] w heq s1 hgetn hgetp; subst N.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.lezP; first by Lia.lia.
    by move=> _ [<-] /= <-.
  move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
  rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
  rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
  case: ssrZ.lezP => // _ [<-].
  move=> [s1' [hbody hwhile]].
  move: hbody => /semE [s1'' []].
  move=> /sem_IE /sem_iE.
  move=> [v [v' []]].
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite /get_gvar hgetp hgetn /= !truncate_word_u /=.
  t_xrbindP=> m1'' hwrites1 ?; subst s1''.
  move=> /semE [s1'' [hsemI hsem]].
  move: hsem => /semE ?; subst s1''.
  move: hsemI => /sem_IE /sem_iE /= [v0 [v0' []]].
  rewrite /get_gvar /= hgetn /= /sem_sop2 /truncate_val /= !truncate_word_u /= => -[<-].
  rewrite /to_word truncate_word_u /= => -[<-] hwn.
  apply: (@vmap_eq_exceptT s1'.(evm)); last first.
  + symmetry.
    apply: vmap_eq_exceptI (vrvP_var hwn).
    move=> x /Sv.add_spec [->|/Sv.empty_spec //]. apply /sv_of_listP. by apply mem_head.
  apply: (ih _ _ (w - wrepr Uptr (wsize_size ws))%R refl_equal)=> //.
  + rewrite wsigned_sub.
    + have := wsize_size_pos ws. Lia.lia.
    have := wsigned_range w.
    have := wsize_size_pos ws.
    have: (wmin_signed Uptr <= - wsize_size ws)%Z.
    + assert (toto := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
      have := wsize_size_wmin_signed ws. Lia.lia.
    Lia.lia.
  + move: hwn; rewrite /write_var.
    t_xrbindP=> ? /= hset <-.
    rewrite (get_var_set_var _ hset) eq_refl /=.
    have /subtypeEl /= := type_of_get_var hgetn.
    move=> [sz' [htyn hlen]].
    rewrite htyn /=. rewrite sumbool_of_boolET /=. done.
  move: hwn; rewrite /write_var.
  t_xrbindP=> ? /= hset <-.
  rewrite (get_var_set_var _ hset).
  case: eqP; congruence.
Qed.

Lemma clear_loop_positive_spec : forall ws (p n:var_i) s1 s2 (w wp : word Uptr),
  p.(v_var) <> n.(v_var) ->
  get_var s1.(evm) n = ok (Vword w) ->
  get_var s1.(evm) p = ok (Vword wp) ->
  sem_I P ev s1 (clear_loop_positive ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ sv_of_list v_var [::n;p] ].
Proof.
  move=> ws p n s1 s2 w wp hneq hgetn hgetp. (*
  case (Z.le_gt_cases 0 (wsigned w)) => [hle|hlt]; last first.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.lezP; first by Lia.lia.
    by move=> _ [<-] /= <-. *)
(*  Search Z "_ind".
  Z_lt_induction
  Zlt_0_ind *)
  have: exists N, (0 <= N /\ wsigned w < N)%Z.
  + exists (wbase Uptr).
    split.
    + assert (hh := @wunsigned_range Uptr 0%R). Lia.lia.
    rewrite wsignedE.
    case: msb.
    + assert (hh := @wunsigned_range Uptr w%R). Lia.lia.
    assert (hh := @wunsigned_range Uptr w%R). Lia.lia.
  move=> [N [hle hlt]].
  move: N hle w hlt s1 hgetn hgetp.
  apply: natlike_ind => [| N hle ih ] w hlt s1 hgetn hgetp.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.lezP; first by Lia.lia.
    by move=> _ [<-] /= <-.
  case (Z.le_gt_cases 0 (wsigned w)) => [hwle|hwlt]; last first.
  + (* we do the work twice *)
    move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.lezP; first by Lia.lia.
    by move=> _ [<-] /= <-.
  move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
  rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
  rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
  case: ssrZ.lezP; last by Lia.lia.
  move=> _ [<-].
  move=> [s1' [hbody hwhile]].
  move: hbody => /semE [s1'' []].
  move=> /sem_IE /sem_iE.
  move=> [v [v' []]].
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite /get_gvar hgetp hgetn /= !truncate_word_u /=.
  t_xrbindP=> m1'' hwrites1 ?; subst s1''.
  move=> /semE [s1'' [hsemI hsem]].
  move: hsem => /semE ?; subst s1''.
  move: hsemI => /sem_IE /sem_iE /= [v0 [v0' []]].
  rewrite /get_gvar /= hgetn /= /sem_sop2 /truncate_val /= !truncate_word_u /= => -[<-].
  rewrite /to_word truncate_word_u /= => -[<-] hwn.
  apply: (@vmap_eq_exceptT s1'.(evm)); last first.
  + symmetry.
    apply: vmap_eq_exceptI (vrvP_var hwn).
    move=> x /Sv.add_spec [->|/Sv.empty_spec //]. apply /sv_of_listP. by apply mem_head.
  apply (ih (w - wrepr Uptr (wsize_size ws))%R) => //.
  + rewrite wsigned_sub.
    + have := wsize_size_pos ws. Lia.lia.
    have := wsigned_range w.
    have := wsize_size_pos ws.
    have: (wmin_signed Uptr <= - wsize_size ws)%Z.
    + assert (toto := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
      have := wsize_size_wmin_signed ws. Lia.lia.
    Lia.lia.
  + move: hwn; rewrite /write_var.
    t_xrbindP=> ? /= hset <-.
    rewrite (get_var_set_var _ hset) eq_refl /=.
    have /subtypeEl /= := type_of_get_var hgetn.
    move=> [sz' [htyn hlen]].
    rewrite htyn /=. rewrite sumbool_of_boolET /=. done.
  move: hwn; rewrite /write_var.
  t_xrbindP=> ? /= hset <-.
  rewrite (get_var_set_var _ hset).
  case: eqP; congruence.
Qed.

Lemma clear_loop_correct : forall ws p (n:var_i) s1 s2 (w : word Uptr),
  get_var s1.(evm) n = ok (Vword w) ->
  sem_I P ev s1 (clear_loop ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ Sv.singleton n ].
Proof.
  move=> ws p n s1 s2 w.
  have [hle _] := wunsigned_range w.
  move: {-2}(wunsigned w) hle (refl_equal (wunsigned w)).
  apply: natlike_ind => [| N hle ih ] heq hget.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hget /= /sem_sop2 /= !truncate_word_u /=.
    rewrite -/(wunsigned _) heq word.urepr_ge0 => -[<-].
    move=> [s1' [
  rewrite wunsigned_repr. Search (0 mod _)%Z. rewrite Zmod_0_l /=. Search (?A <= ?A)%R. Order.le_refl
  Search word.urepr wunsigned.
  
  move=> /semE.
    re
    case: (clear_loop ws p n) => [ii ir] /sem_iE.
  - 
  elim/natlike_ind. : N. w .