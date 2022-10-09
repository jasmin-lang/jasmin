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

(* n is non-negative and decreasing *)
Definition clear_loop_positive_counter ws p n :=
  let off := Papp2 (Omul (Op_w Uptr)) (pword_of_int Uptr (wsize_size ws)) (Pvar (mk_lvar n)) in
  let ir1 :=
    Cassgn (Lmem ws p off) AT_keep (sword ws) (pword_of_int ws 0) in
  let ir2 :=
    Cassgn (Lvar n) AT_keep (sword Uptr) (Papp2 (Osub (Op_w Uptr)) (Pvar (mk_lvar n)) (pword_of_int Uptr 1)) in
  let body :=
    map (MkI dummy_instr_info) [:: ir2; ir1] in
  let ir := Cwhile NoAlign [::] (Papp2 (Olt (Cmp_w Signed Uptr)) (pword_of_int Uptr 0) (Pvar (mk_lvar n))) body in
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

Lemma wsigned_sub_if (ws : wsize) (a b : word ws) :
  wsigned (a - b) =
    if (wmax_signed ws <? wsigned a - wsigned b)%Z then (wsigned a - wsigned b - wbase ws)%Z
    else if (wsigned a - wsigned b <? wmin_signed ws)%Z then (wsigned a - wsigned b + wbase ws)%Z
    else (wsigned a - wsigned b)%Z.
Proof.
Admitted.

Lemma wsigned_add sz p n :
  (wmin_signed sz <= wsigned p + n <= wmax_signed sz)%Z ->
  wsigned (p + wrepr sz n) = (wsigned p + n)%Z.
Proof.
Admitted.

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

(* We use an ind principle tailored to our needs: in the inductive case, we want to consider
  only non-negative [x] but we want to allow the induction hypothesis to use negative [y].
  This is true because we request on top of that that [P] holds on all negative ints.
*)
Lemma Z_better_ind2 : forall P : Z -> Prop,
(forall x : Z, (x <= 0)%Z -> P x) ->
(forall x : Z, (forall y : Z, (y < x)%Z -> P y) -> (0 < x)%Z -> P x) ->
forall x : Z, P x.
Proof.
  intros Q Hneg Hpos x.
  set (Q' := fun x => Q (Z.succ x)).
  have: Q' (Z.pred x).
  + destruct (Z.le_gt_cases 0 (Z.pred x)); last first.
    + apply Hneg. Lia.lia.
    revert H.
    apply Zlt_0_ind; clear x.
    intros. apply Hpos; try Lia.lia. intros.
    destruct (Z.le_gt_cases y 0); last first.
    + rewrite -(Z.succ_pred y). apply H. Lia.lia.
    apply Hneg. Lia.lia.
  rewrite -{2}(Z.succ_pred x). apply.
Qed.

Lemma clear_loop_positive_counter_eq_0 : forall ws (p n : var_i) s1 s2 (w : word Uptr),
  get_var s1.(evm) n = ok (Vword w) ->
  (0 <= wsigned w)%Z ->
  sem_I P ev s1 (clear_loop_positive_counter ws p n) s2 ->
  exists (w2 : word Uptr), get_var s2.(evm) n = ok (Vword w2) /\ wsigned w2 = 0%Z.
Proof.
  move=> ws p n s1 s2 w hgetn hle0.
  move: w {2}(wsigned w) (refl_equal (wsigned w)) s1 hgetn hle0 => w0 N; move: N w0.
  apply: Z_better_ind2 => [N hlt|N ih hle] w ? s1 hgetn hle0; subst N.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar /= hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.ltzP; first by Lia.lia.
    move=> _ [<-] <-.
    exists w. split=> //. Lia.lia.
  move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
  rewrite /get_gvar /= hgetn /= /sem_sop2 /= !truncate_word_u /=.
  rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
  case: ssrZ.ltzP; last by Lia.lia.
  move=> _ [<-] /=.
  move=> [s1' [hbody hwhile]].
  move: hbody => /semE [s1'' []].
  move=> /sem_IE /sem_iE.
  move=> [v [v' []]].
  rewrite /= /get_gvar /= hgetn /= /sem_sop2 /truncate_val /= !truncate_word_u /= => -[<-].
  rewrite /to_word truncate_word_u /= => -[<-].
  rewrite /write_var. t_xrbindP=> vm1 hset ?; subst s1''.
  move=> /semE [s1'' [hsemI hsem]].
  move: hsem => /semE ?; subst s1''.
  move: hsemI => /sem_IE /sem_iE /= [v0 [v0' []]].
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite /get_gvar /= (get_var_set_var _ hset) eq_refl.
  have /subtypeEl /= := type_of_get_var hgetn.
  move=> [sz' [htyn hlen]].
  rewrite htyn /=. rewrite sumbool_of_boolET /=.
  t_xrbindP=> wp vp hgetp hwp ? _ _ _ ? _ m1'' hwrites1 ?; subst s1'.
  apply: (ih (wsigned w - 1)%Z _ (w-wrepr Uptr 1)%R _ (with_mem (with_vm s1 vm1) m1'')).
  + by Lia.lia.
  + rewrite wsigned_sub. done.
    have := wsigned_range w.
    assert (hh := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
    have := wsize_size_wmin_signed U8.
    rewrite /=. Lia.lia.
  + rewrite /= (get_var_set_var _ hset) eq_refl.
    rewrite htyn /=. rewrite sumbool_of_boolET /=. done.
  + rewrite wsigned_sub. Lia.lia.
    have := wsigned_range w.
    assert (hh := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
    have := wsize_size_wmin_signed U8.
    rewrite /=. Lia.lia.
  done.
Qed.

(* apparently it is simpler to work with srepr *)
Lemma wsigned_inj ws : injective (@wsigned ws).
Proof.
  move=> w1 w2.
  rewrite !wsignedE.
  case: msb; case: msb.
  + move=> ?.
    have: wunsigned w1 = wunsigned w2 by Lia.lia.
    by apply wunsigned_inj.
  + have := wunsigned_range w1.
    have := wunsigned_range w2. Lia.lia.
  + have := wunsigned_range w1.
    have := wunsigned_range w2. Lia.lia.
  by apply wunsigned_inj.
Qed.

Lemma wmin_signed_neg ws : (wmin_signed ws < 0)%Z.
Proof.
  have /= := wmin_signed_m _ _ (wsize_le_U8 ws).
  have /= := wsize_size_wmin_signed U8. Lia.lia.
Qed.

(* TODO: imitate the proof of wmin_signed_neg *)
Lemma wmax_signed_pos ws : (0 < wmax_signed ws)%Z.
Proof.
  by case: ws.
Qed.

Lemma clear_loop_positive_counter_spec_disj : forall ws (p n:var_i) s1 s2 (w wp : word Uptr),
  p.(v_var) <> n.(v_var) ->
  get_var s1.(evm) n = ok (Vword w) ->
  get_var s1.(evm) p = ok (Vword wp) ->
  sem_I P ev s1 (clear_loop_positive_counter ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ Sv.singleton n ] /\
  forall p sz, disjoint_zrange wp (wsigned w * wsize_size ws)%Z p (wsize_size sz) ->
    read s2.(emem) p sz = read s1.(emem) p sz.
Proof.
  move=> ws p n s0 s2 w0 wp hneq hgetn0 hgetp hsem.
  have: (wsigned w0 < 0 -> wsigned w0 = wsigned w0)%Z ->
    (0 <= wsigned w0 -> 0 <= wsigned w0)%Z ->
    evm s2 = evm s0 [\ Sv.singleton n] /\
      forall p sz, disjoint_zrange wp (wsigned w0 * wsize_size ws)%Z p (wsize_size sz) ->
        read s2.(emem) p sz = read s0.(emem) p sz; last first.
  + move=> /(_ (fun _ => refl_equal) (fun h => h)) [h1 h2]. split. done.
    by move=> i; eauto.

  (* the administrative stuff is painful and ugly *)
  move: {-3 5 6}(w0) {2}(wsigned w0) (refl_equal (wsigned w0)) (s0) (hgetn0) hgetp hsem => w N; move: N w.
  apply: Z_better_ind2 => [N hlt|N ih hle] w heq s1 hgetn hgetp; subst N.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.ltzP; first by Lia.lia.
    move=> _ [<-] /= <-. move=> hneg hnneg. done.
  move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
  rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
  rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
  case: ssrZ.ltzP; last by Lia.lia.
  move=> _ [<-].
  move=> [s1' [hbody hwhile]].
  move: hbody => /semE [s1'' []].
  move=> /sem_IE /sem_iE.
  move=> [v [v' []]].
  rewrite /= /get_gvar /= hgetn /= /sem_sop2 /truncate_val /= !truncate_word_u /= => -[<-].
  rewrite /to_word truncate_word_u /= => -[<-].
  rewrite /write_var; t_xrbindP=> vm1 hset ?; subst s1''.
  move=> /semE [] s1'' [].
  move=> /sem_IE /sem_iE /= [v0 [v0' []]].
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite /get_gvar /= !(get_var_set_var _ hset) eq_refl.
  case: eqP; first by congruence.
  move=> _; rewrite hgetp /= !truncate_word_u /=.
  rewrite /sem_sop2 /= !truncate_word_u /=.
  have /subtypeEl /= := type_of_get_var hgetn.
  move=> [sz' [htyn hlen]].
  rewrite htyn /=. rewrite sumbool_of_boolET /= wrepr1.
  rewrite truncate_word_u /= truncate_word_u /=.
  t_xrbindP=> m1 hm1 ?; subst s1''.
  move=> /semE ?; subst s1'.
  move=> hneg hnneg.
  have: evm s2 = vm1 [\Sv.singleton n] /\
        forall (ptr : word Uptr) (sz : wsize),
          disjoint_zrange wp (wsigned (w-1) * wsize_size ws) ptr (wsize_size sz) ->
         read (emem s2) ptr sz = read m1 ptr sz.
  + apply: (ih _ _ _ refl_equal (Estate _ _ _)).
    + rewrite -wrepr1. rewrite wsigned_sub.
      Lia.lia.
      have := wsigned_range w.
      assert (toto := wmin_signed_neg Uptr). by Lia.lia.
    + rewrite /=.
      rewrite (get_var_set_var _ hset) eq_refl.
      rewrite htyn /=. rewrite sumbool_of_boolET /= wrepr1. done.
    + rewrite /=.
      rewrite (get_var_set_var _ hset).
      case: eqP; congruence.
    + constructor. eassumption.
    + move=> /[dup] /hneg. Lia.lia.
    move=> _. rewrite -wrepr1 wsigned_sub. Lia.lia.
    have := wsigned_range w.
    assert (toto := wmin_signed_neg Uptr). Lia.lia.
  move=> [hvmeq hmem'].
  split.
  + rewrite hvmeq.
    rewrite SvP.MP.singleton_equal_add.
    symmetry.
    apply: (vrvP_var (v:=Vword (s:=Uptr) (w - wrepr Uptr 1)) (s2:=Estate _ _ _)).
    rewrite /write_var. rewrite /= hset /=. reflexivity.
  move=> ptr sz hptr. rewrite hmem'; last first.
  + apply: disjoint_zrange_incl_l hptr.
    apply zbetween_le.
    rewrite -wrepr1. rewrite wsigned_sub; last first.
    + assert (toto := wmin_signed_neg Uptr).
      have := wsigned_range w. Lia.lia.
    rewrite Z.mul_sub_distr_r Z.mul_1_l.
    have := wsize_size_pos ws. Lia.lia.
  apply (writeP_neq hm1).
  apply: disjoint_zrange_incl_l (hptr).
  rewrite /zbetween !zify.
  rewrite -{-3}(wrepr_signed w) -wrepr1 -wrepr_sub -wrepr_mul.
  rewrite wunsigned_add; last first.
  + case: hptr. move=> + _ _.
    rewrite /no_overflow !zify.
    have := wsize_size_pos ws.
    have := wunsigned_range wp. Lia.nia.
  have := wsize_size_pos ws. Lia.nia.
Qed.

Lemma clear_loop_positive_counter_spec : forall ws (p n:var_i) s1 s2 (w wp : word Uptr),
  p.(v_var) <> n.(v_var) ->
  get_var s1.(evm) n = ok (Vword w) ->
  get_var s1.(evm) p = ok (Vword wp) ->
  sem_I P ev s1 (clear_loop_positive_counter ws p n) s2 ->
  forall i, (0 <= i < wsigned w * wsize_size ws)%Z ->
    read s2.(emem) (wp + wrepr _ i)%R U8 = ok 0%R.
Proof.
  move=> ws p n s0 s2 w0 wp hneq hgetn0 hgetp hsem.
  have: (wsigned w0 < 0 -> wsigned w0 = wsigned w0)%Z ->
    (0 <= wsigned w0 -> 0 <= wsigned w0)%Z ->
    (forall i, read s2.(emem) (wp + wrepr _ i)%R U8 = ok 0%R \/
               read s2.(emem) (wp + wrepr _ i)%R U8 = read s0.(emem) (wp + wrepr _ i)%R U8) /\
      (forall i, (0 <= i < wsigned w0 * wsize_size ws)%Z ->
        read s2.(emem) (wp + wrepr _ i)%R U8 = ok 0%R); last first.
  + move=> /(_ (fun _ => refl_equal) (fun h => h)) [h1 h2]. done.

  (* the administrative stuff is painful and ugly *)
  move: {-3 5 6}(w0) {2}(wsigned w0) (refl_equal (wsigned w0)) (s0) (hgetn0) hgetp hsem => w N; move: N w.
  apply: Z_better_ind2 => [N hlt|N ih hle] w heq s1 hgetn hgetp; subst N.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.ltzP; first by Lia.lia.
    move=> _ [<-] /= <-. move=> hneg hnneg. split.
    + move=> i. right. done.
    move=> i. (*
    rewrite wsigned_sub_if.
    case: ZltP.
    + have := wsigned_range w0.
      case: (Z.le_gt_cases 0 (wsigned w0)).
      + by move=> /hnneg; Lia.lia.
      move=> /hneg. assert (toto := wmax_signed_pos Uptr). Lia.lia.
    move=> ?.
    case: ZltP.
    + have := wsigned_range w0.
      case: (Z.le_gt_cases 0 (wsigned w0)).
      + by move=> /hnneg; Lia.lia.
      move=> /hneg. Lia.lia. *)
    have := wsize_size_pos ws. by Lia.lia.
  move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
  rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
  rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
  case: ssrZ.ltzP; last by Lia.lia.
  move=> _ [<-].
  move=> [s1' [hbody hwhile]].
  move: hbody => /semE [s1'' []].
  move=> /sem_IE /sem_iE.
  move=> [v [v' []]].
  rewrite /= /get_gvar /= hgetn /= /sem_sop2 /truncate_val /= !truncate_word_u /= => -[<-].
  rewrite /to_word truncate_word_u /= => -[<-].
  rewrite /write_var; t_xrbindP=> vm1 hset ?; subst s1''.
  move=> /semE [] s1'' [].
  move=> /sem_IE /sem_iE /= [v0 [v0' []]].
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite /get_gvar /= !(get_var_set_var _ hset) eq_refl.
  case: eqP; first by congruence.
  move=> _; rewrite hgetp /= !truncate_word_u /=.
  rewrite /sem_sop2 /= !truncate_word_u /=.
  have /subtypeEl /= := type_of_get_var hgetn.
  move=> [sz' [htyn hlen]].
  rewrite htyn /=. rewrite sumbool_of_boolET /= wrepr1.
  rewrite truncate_word_u /= truncate_word_u /=.
  t_xrbindP=> m1 hm1 ?; subst s1''.
  move=> /semE ?; subst s1'.
  move=> hneg hnneg.
  have: (forall i,
          read s2.(emem) (wp + wrepr _ i)%R U8 = ok 0%R \/
          read s2.(emem) (wp + wrepr _ i)%R U8 = read m1 (wp + wrepr _ i)%R U8
          ) /\
        (forall i, (0 <= i < wsigned (w-1) * wsize_size ws)%Z ->
          read s2.(emem) (wp + wrepr _ i)%R U8 = ok 0%R).
  + apply: (ih _ _ _ refl_equal (with_mem (with_vm s1 vm1) m1)).
    + rewrite -wrepr1. rewrite wsigned_sub.
      Lia.lia.
      have := wsigned_range w.
      assert (toto := wmin_signed_neg Uptr). by Lia.lia.
    + rewrite /=.
      rewrite (get_var_set_var _ hset) eq_refl.
      rewrite htyn /=. rewrite sumbool_of_boolET /= wrepr1. done.
    + rewrite /=.
      rewrite (get_var_set_var _ hset).
      case: eqP; congruence.
    + constructor. apply hwhile.
    + move=> /[dup] /hneg. Lia.lia.
    move=> _. rewrite -wrepr1 wsigned_sub. Lia.lia.
    have := wsigned_range w.
    assert (toto := wmin_signed_neg Uptr). Lia.lia.
  move=> [hmem1 hmem2].
  split.
  + move=> i.
    case: (hmem1 i).
    + left; assumption.
    move=> ->.
    rewrite (write_read8 hm1) /=.
    case: andb.
    + left.
      rewrite /LE.wread8 /LE.encode /split_vec.
      have hmod: forall (ws:wsize), ws %% U8 = 0%nat.
      + by move=> [].
      have hdiv: forall (ws:wsize), ws %/ U8 = Z.to_nat (wsize_size ws).
      + by move=> [].
      case: (Nat.le_gt_cases (size (iota 0 (ws %/ U8 + ws %% U8)))
        (Z.to_nat (sub (wp + wrepr Uptr i) (wp + wrepr Uptr (wsize_size ws) * (w - 1)))))%R.
      + move=> ?.
        rewrite nth_default //. apply /leP.
        rewrite size_map. done.
      move=> ?.
      rewrite (nth_map 0); last first.
      + by apply /ltP.
      rewrite hmod hdiv.
      rewrite /word.subword /=. rewrite Z.shiftr_0_l.
      rewrite Zmod_0_l. f_equal. apply /(@eqP (word U8)). done.
    by right.
  move=> i hi.
  destruct (Z.le_gt_cases (wsigned w * wsize_size ws - wsize_size ws) i).
  + case: (hmem1 i) => // ->.
    rewrite (write_read8 hm1).
    rewrite subE {1}(GRing.addrC wp) GRing.addrKA.
    rewrite -(wrepr_signed w) -wrepr1 -wrepr_sub -wrepr_mul -wrepr_sub.
    rewrite Z.mul_comm. rewrite Z.mul_sub_distr_r Z.mul_1_l Z.sub_sub_distr.
    rewrite wunsigned_repr.
    rewrite Zmod_small; last first.
    + split. Lia.lia. have := wsize_size_wbase ws.
      assert (toto := wbase_m (wsize_le_U8 Uptr)).
      rewrite -/(wbase _). Lia.lia.
    move=> /=.
    case: andP; rewrite !zify; last by Lia.lia.
    move=> _.
    rewrite /LE.wread8 /LE.encode /split_vec.
    have hmod: forall (ws:wsize), ws %% U8 = 0%nat.
    + by move=> [].
    have hdiv: forall (ws:wsize), ws %/ U8 = Z.to_nat (wsize_size ws).
    + by move=> [].
    rewrite (nth_map 0); last first.
    + rewrite size_iota. rewrite hmod hdiv. apply /ltP.
      rewrite addn0. Lia.lia.
    rewrite hmod hdiv.
    rewrite /word.subword /=. rewrite Z.shiftr_0_l.
    rewrite Zmod_0_l. f_equal. apply /(@eqP (word U8)). done.
  apply hmem2.
  rewrite -wrepr1 wsigned_sub. Lia.lia.
  assert (toto := wmin_signed_neg Uptr).
  have := wsigned_range w. Lia.lia.
Qed.

Lemma clear_loop_positive_spec : forall ws (p n:var_i) s1 s2 (w wp : word Uptr),
  p.(v_var) <> n.(v_var) ->
  get_var s1.(evm) n = ok (Vword w) ->
  get_var s1.(evm) p = ok (Vword wp) ->
  sem_I P ev s1 (clear_loop_positive ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ Sv.singleton n ] /\
  forall i,
    read s2.(emem) (wp + wrepr _ i)%R U8 =
      if (0 <=? i)%Z && (i <? wsigned w)%Z then ok 0%R
      else read s1.(emem) (wp + wrepr _ i)%R U8.
Proof.
  move=> ws p n s1 s2 w0 wp hneq hgetn hgetp hsem.
  have: evm s2 = evm s1 [\ Sv.singleton n] /\
    exists w,
      get_var s2.(evm) n = ok (Vword w) /\
      (forall i : Z,
        read (emem s2) (wp + wrepr Uptr i)%R U8 =
         if (0 <=? i)%Z && (i <? wsigned (w0 - w))%Z then ok 0%R
         else read (emem s1) (wp + wrepr Uptr i)%R U8); last first.
 + move=> [h1 [w [h2 h3]]]. split. done. done.
  (* the administrative stuff is painful and ugly *)
  move: w0 wp0 {2}(wsigned w0) (refl_equal (wsigned w0)) s0 hgetn0 hgetp0 hsem => w0 wp0 N; move: N w0 wp0.
  apply: Z_better_ind => [N hlt|N ih hle] w wp heq s1 hgetn hgetp; subst N.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.lezP; first by Lia.lia.
    move=> _ [<-] /= <-. split.
    + done.
    + exists w, wp. split=> //. split=> //. move=> i.
      case: andP => //.
      by rewrite !zify; Lia.lia.
    
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