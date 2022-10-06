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
    map (MkI dummy_instr_info) [:: ir1; ir2] in
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
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite /get_gvar hgetn /= !truncate_word_u /=.
  t_xrbindP=> wp vp hgetp hwp ? _ _ _ m1'' hwrites1 ?; subst s1''.
  move=> /semE [s1'' [hsemI hsem]].
  move: hsem => /semE ?; subst s1''.
  move: hsemI => /sem_IE /sem_iE /= [v0 [v0' []]].
  rewrite /get_gvar /= hgetn /= /sem_sop2 /truncate_val /= !truncate_word_u /= => -[<-].
  rewrite /to_word truncate_word_u /= => -[<-] hwn.
  apply: (ih (wsigned w - 1)%Z _ (w-wrepr Uptr 1)%R _ s1').
  + by Lia.lia.
  + rewrite wsigned_sub. done.
    have := wsigned_range w.
    assert (hh := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
    have := wsize_size_wmin_signed U8.
    rewrite /=. Lia.lia.
  + move: hwn; rewrite /write_var.
    t_xrbindP=> ? hset <- /=.
    rewrite (get_var_set_var _ hset) eq_refl.
    have /subtypeEl /= := type_of_get_var hgetn.
    move=> [sz' [htyn hlen]].
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

Lemma clear_loop_positive_counter_spec : forall ws (p n:var_i) s1 s2 (w wp : word Uptr),
  p.(v_var) <> n.(v_var) ->
  get_var s1.(evm) n = ok (Vword w) ->
  get_var s1.(evm) p = ok (Vword wp) ->
  sem_I P ev s1 (clear_loop_positive_counter ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ Sv.singleton n ] /\
  forall i,
    read s2.(emem) (wp + wrepr _ i)%R U8 =
      if (0 <=? i)%Z && (i <? wsigned w * wsize_size ws)%Z then ok 0%R
      else read s1.(emem) (wp + wrepr _ i)%R U8.
Proof.
  move=> ws p n s1 s2 w0 wp hneq hgetn hgetp hsem.
  have: evm s2 = evm s1 [\ Sv.singleton n] /\
    exists w,
      get_var s2.(evm) n = ok (Vword w) /\
      (forall i : Z,
        read (emem s2) (wp + wrepr Uptr i)%R U8 =
         if (0 <=? i)%Z && (i <? wsigned (w0 - w) * wsize_size ws)%Z then ok 0%R
         else read (emem s1) (wp + wrepr Uptr i)%R U8); last first.
  + move=> [h1 [w [h2 h3]]]. split. done.
    destruct (Z.le_gt_cases (wsigned w0) 0).
    + move=> i. admit.
    move=> i. rewrite h3.
    have: w = 0%R.
    + apply wsigned_inj. rewrite wsigned0.
      have [] := clear_loop_positive_counter_eq_0 _ _ _ _ _ _ hgetn _ hsem; first by Lia.lia.
      rewrite h2.
      move=> ? [] [] <-. done.
    move=> ->. rewrite GRing.subr0. done.

  (* the administrative stuff is painful and ugly *)
  move: w0 {2}(wsigned w0) (refl_equal (wsigned w0)) s1 hgetn hgetp hsem => w0 N; move: N w0.
  apply: Z_better_ind2 => [N hlt|N ih hle] w heq s1 hgetn hgetp; subst N.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.ltzP; first by Lia.lia.
    move=> _ [<-] /= <-. split.
    + done.
    + exists w. split=> //. move=> i.
      case: andP => //.
      rewrite GRing.subrr wsigned0.
      by rewrite !zify; Lia.lia.
  move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
  rewrite /get_gvar hgetn /= /sem_sop2 /= !truncate_word_u /=.
  rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
  case: ssrZ.ltzP; last by Lia.lia.
  move=> _ [<-].
  move=> [s1' [hbody hwhile]].
  move: hbody => /semE [s1'' []].
  move=> /sem_IE /sem_iE.
  move=> [v [v' []]].
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite /get_gvar hgetp hgetn /= !truncate_word_u /=.
  rewrite /sem_sop2 /= !truncate_word_u /= !truncate_word_u /=.
  t_xrbindP=> m1'' hwrites1 ?; subst s1''.
  move=> /semE [s1'' [hsemI hsem]].
  move: hsem => /semE ?; subst s1''.
  move: hsemI => /sem_IE /sem_iE /= [v0 [v0' []]].
  rewrite /get_gvar /= hgetn /= /sem_sop2 /truncate_val /= !truncate_word_u /= => -[<-].
  rewrite /to_word truncate_word_u /= => -[<-] hwn.
  have: evm s2 = evm s1' [\Sv.singleton n] /\
    exists w' : word Uptr,
        get_var (evm s2) n = ok (Vword (s:=Uptr) w') /\
        (forall i : Z,
         read (emem s2) (wp + wrepr Uptr i)%R U8 =
         (if (0 <=? i)%Z && (i <? wsigned (w - 1 - w') * wsize_size ws)%Z
          then ok 0%R
          else read (emem s1') (wp + wrepr Uptr i)%R U8)).
  + apply: (ih _ _ _ refl_equal).
    + rewrite -wrepr1. rewrite wsigned_sub.
      Lia.lia.
      have := wsigned_range w.
      assert (toto := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
      have /= := wsize_size_wmin_signed U8. Lia.lia.
    + move: hwn; rewrite /write_var; t_xrbindP=> ? /= hset <-.
      rewrite (get_var_set_var _ hset) eq_refl.
      have /subtypeEl /= := type_of_get_var hgetn.
      move=> [sz' [htyn hlen]].
      rewrite htyn /=. rewrite sumbool_of_boolET /= wrepr1. done.
    + move: hwn; rewrite /write_var; t_xrbindP=> ? /= hset <-.
      rewrite (get_var_set_var _ hset).
      case: eqP; congruence.
    + done.
  move=> [hvmeq [w' [hgetn' hmem']]].
  split.
  + rewrite hvmeq.
    rewrite SvP.MP.singleton_equal_add.
    symmetry.
    by apply: vrvP_var hwn.
  exists w'; split=> //.
  move=> i; rewrite hmem'.
  move: hwn; rewrite /write_var; t_xrbindP => ? /= hset ? /=; subst s1'.
  rewrite -GRing.addrA (GRing.addrC (-1)%R) GRing.addrA.
  rewrite -wrepr1. rewrite wsigned_sub; last first.
  + have : exists w2 : word Uptr, get_var (evm s2) n = ok (Vword (s:=Uptr) w2) /\ wsigned w2 = 0%Z.
    + apply: clear_loop_positive_counter_eq_0. 3:constructor; eassumption.
      rewrite (get_var_set_var _ hset) eq_refl.
      have /subtypeEl /= := type_of_get_var hgetn.
      move=> [sz' [htyn hlen]].
      rewrite htyn /=. rewrite sumbool_of_boolET /=. done.
    rewrite wsigned_sub; first by Lia.lia.
    have := wsigned_range w.
    assert (toto := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
    have /= := wsize_size_wmin_signed U8. Lia.lia.
  rewrite hgetn'.
  move=> [io [[] ?]]; subst io.
  rewrite -(wsigned0 Uptr) => /wsigned_inj ?; subst w'.
  rewrite GRing.subr0.
  have := wsigned_range w.
  assert (toto := wmin_signed_m _ _ (wsize_le_U8 Uptr)).
  have /= := wsize_size_wmin_signed U8. Lia.lia.
  
    
  
   clear_loop_positive_counter_eq_0 _ _ _ _ _ _ _ _ hwhile.
  Search w'.
  rewrite Z.mul_sub_distr_r Z.mul_1_l.
  case: andP; case: andP; rewrite !zify => //.
  + by have:=wsize_size_pos ws; Lia.lia.
  + admit.
  move=> ??.
  rewrite (write_read8 hwrites1). rewrite subE.
  rewrite {1}(GRing.addrC wp) GRing.addrKA.
  rewrite -(wrepr_unsigned w).
  rewrite -wrepr_mul. rewrite -wrepr_sub. rewrite wunsigned_repr.
  cbn [iota].
  case: andP; rewrite !zify. admit. Lia.lia.
  have: (wp + wrepr Uptr i - (wp + wrepr Uptr (wsize_size ws) * w) = wrepr Uptr i - wrepr Uptr (wsize_size ws) * w)%R.
  + ssrring.ssring.
  
  ; try Lia.lia.
  + move=> ??.
    rewrite (write_read8 hwrites1) /=.
    rewrite subE. 
    rewrite (writeP_neq hwrites1). done.
    rewrite /disjoint_range /disjoint_zrange.
    
  Search write read.
  have := write_read8 hwrites1 (wp + wrepr Uptr (wsize_size ws) * w')%R.
  Search (sub (_ +_)%R). subE
  case: andP.

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