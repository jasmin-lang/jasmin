From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice tuple.
From mathcomp Require Import div fintype order ssralg ssrnum word_ssrZ word.
From Coq Require Zquot.
From Coq Require Import ZArith.
Require Import utils.
Require Import wsize.
Require Import word.
Import Utf8 Lia.
Import word_ssrZ.
Import GRing.Theory Num.Theory Order.POrderTheory Order.TotalTheory.
Import ssrnat.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
Local Open Scope Z_scope.
Ltac elim_div :=
   unfold Z.div, Z.modulo;
     match goal with
       |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
       |  |-  context[ Z.div_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
     end; unfold Remainder.

Lemma wbase_pos ws :
  (wbase ws > 0)%Z.
Proof. by case: ws. Qed.

Lemma wsize_sizeE sz : 8 * wsize_size sz =  wsize_bits sz.
Proof. by case: sz. Qed.

Lemma wbase_div_wbase ws0 ws1 :
  (ws0 <= ws1)%CMP ->
  (wbase ws0 | wbase ws1).
Proof. move=> h. exists (wbase ws1 / wbase ws0). case: ws0 h; by case: ws1. Qed.

Lemma mul_wordE {ws} (w1 w2 : word ws) : (w1 * w2)%w = (w1 * w2)%R.
Proof. reflexivity. Qed.

Lemma opp_wordE {ws} (w : word ws) : (- w)%w = (-w)%R.
Proof. reflexivity. Qed.

Lemma word0E {ws} : (0%w : word ws) = 0%R.
Proof. reflexivity. Qed.

Lemma word1E {ws} : (1%w : word ws) = 1%R.
Proof. reflexivity. Qed.

Lemma wunsigned1 ws :
  @wunsigned ws 1 = 1%Z.
Proof. by case: ws. Qed.

Lemma wrepr_signed s (w: word s) : wrepr s (wsigned w) = w.
Proof. by rewrite /wrepr /wsigned sreprK. Qed.

Lemma wrepr1 sz : wrepr sz 1 = 1%R.
Proof. by apply/eqP;case sz. Qed.

Lemma wrepr_mod ws k : wrepr ws (k mod wbase ws) = wrepr ws k.
Proof. by apply wunsigned_inj; rewrite !wunsigned_repr Zmod_mod. Qed.

Lemma wunsigned0 ws : @wunsigned ws 0 = 0.
Proof. by rewrite -wrepr0 wunsigned_repr Zmod_0_l. Qed.

Lemma wunsigned_eqb0 ws (w : word ws) : (wunsigned w =? 0) = (w == 0%R).
Proof.
apply/idP/idP => [/ZeqbP h1 | /eqP ->]; last by rewrite wunsigned0; apply/ZeqbP.
by apply/eqP/wunsigned_inj; rewrite h1 wunsigned0.
Qed.

Lemma wunsigned_add_if ws (a b : word ws) :
  wunsigned (a + b) =
   if wunsigned a + wunsigned b <? wbase ws then wunsigned a + wunsigned b
   else wunsigned a + wunsigned b - wbase ws.
Proof.
  move: (wunsigned_range a) (wunsigned_range b).
  rewrite /wunsigned mathcomp.word.word.addwE /GRing.add /= -/(wbase ws) => ha hb.
  case: ZltP => hlt.
  + by rewrite Zmod_small //; lia.
  by rewrite -(Z_mod_plus_full _ (-1)) Zmod_small; lia.
Qed.

Lemma wunsigned_opp_if ws (a : word ws) :
  wunsigned (-a) = if wunsigned a == 0 then 0 else wbase ws - wunsigned a.
Proof.
  have ha := wunsigned_range a.
  rewrite -(GRing.add0r (-a)%R) wunsigned_sub_if wunsigned0.
  by case: ZleP; case: eqP => //; lia.
Qed.

Lemma wunsigned_add_mod ws ws' (w1 w2 : word ws) :
  wunsigned (w1 + w2) mod wsize_size ws' = (wunsigned w1 + wunsigned w2) mod wsize_size ws'.
Proof.
  rewrite wunsigned_add_if.
  case: ZltP => // _.
  rewrite Zminus_mod.
  rewrite (Znumtheory.Zdivide_mod _ _ (wsize_size_div_wbase _ _)) Z.sub_0_r.
  by rewrite Zmod_mod.
Qed.

Lemma wlt_irrefl sz sg (w: word sz) :
  wlt sg w w = false.
Proof. case: sg; exact: Z.ltb_irrefl. Qed.

Lemma wle_refl sz sg (w: word sz) :
  wle sg w w = true.
Proof. case: sg; exact: Z.leb_refl. Qed.

Lemma high_bits_wbase sz n :
  high_bits sz n = wrepr sz (n / wbase sz).
Proof. by rewrite /high_bits Z.shiftr_div_pow2 // wsize_bitsE -wbaseE. Qed.

Lemma wbase_twice_half sz :
  wbase sz = 2 * half_modulus sz.
Proof. done. Qed.

Lemma wsigned_alt sz (w: word sz) :
  let m := half_modulus sz in
  wsigned w = wunsigned (w + wrepr sz m) - m.
Proof.
  rewrite /wsigned sreprE /= -/(wunsigned _) wunsigned_add_if wunsigned_repr_small; last first.
  + by clear; case: sz.
  rewrite /wbase modulusS mulr2n -/(half_modulus _).
  move: (half_modulus _) => m.
  rewrite /Order.lt /GRing.add /GRing.opp /=.
  case: ltZP; case: ltZP; lia.
Qed.

Lemma wsigned_range sz (p: word sz) :
  wmin_signed sz <= wsigned p <= wmax_signed sz.
Proof.
  rewrite wsigned_alt; set q := (_ + _)%R.
  have := wunsigned_range q.
  rewrite /wmin_signed /wmax_signed -/(half_modulus _) wbase_twice_half.
  lia.
Qed.

Lemma wsigned_range_m szi szo:
  (szi ≤ szo)%CMP ->
  (wmin_signed szo <= wmin_signed szi /\ wmax_signed szi <= wmax_signed szo)%Z.
Proof. by case: szi; case: szo. Qed.

Lemma wsar_alt sz (x: word sz) n :
  wsar x n = wsar_naive x n.
Proof.
  rewrite /wsar /wsar_naive.
  case: (Z.min_spec (wsize_bits sz) n) => - [] h ->; last reflexivity.
  have [h0 hx] := wsigned_range x.
  case: (Z.neg_nonneg_cases (wsigned x)); last first.
  + move => {}h0.
    have hr : 0 <= wsigned x < wbase sz.
    - move: hx; rewrite /wmax_signed wbase_twice_half; lia.
    have ? := log2_wsize_bits hr.
    rewrite !Z.shiftr_eq_0 //.
    lia.
  move => {}hx.
  have hr : 0 <= -wsigned x < wbase sz.
  - move: h0; rewrite /wmin_signed wbase_twice_half; lia.
  have hrlog := log2_wsize_bits hr.
  have ? : 0 <= wsize_bits sz by case: (sz).
  have ? : 0 <= n by lia.
  rewrite !Z.shiftr_div_pow2 // -(Z.opp_involutive (wsigned x)) !(Z.div_opp_l_nz (- wsigned x)); only 2, 4: lia.
  + rewrite -!Z.shiftr_div_pow2 // !Z.shiftr_eq_0 //; lia.
  all: rewrite Z.mod_small ?Z.log2_lt_pow2; lia.
Qed.

Lemma wbit_nE ws (w : word ws) i :
  wbit_n w i = Z.odd (wunsigned w / 2 ^ Z.of_nat i)%Z.
Proof.
  have [hlo _] := wunsigned_range w.
  rewrite /wbit_n.
  rewrite word.wbitE; last by rewrite !zify.

  rewrite -(Nat2Z.id (_ %/ _)).

  rewrite -oddZE; last first.
  - rewrite !zify. exact: Zle_0_nat.

  rewrite divnZE; first last.
  - apply: lt0n_neq0. by rewrite expn_gt0.

  rewrite Z2Nat.id; last done.
  by rewrite Nat2Z.n2zX expZE.
Qed.

Lemma wbit_higher_bits_0 x n ws (i : nat) :
  (0 <= n)%Z
  -> (0 <= x < 2 ^ n)%Z
  -> (n <= Z.of_nat i < Z.of_nat (wsize_size_minus_1 ws).+1)%Z
  -> wbit_n (wrepr ws x) i = false.
Proof.
  set m := Z.of_nat (wsize_size_minus_1 ws).+1.
  move=> h0n [h0x hxn] [hni him].

  rewrite wbit_nE.
  rewrite Zdiv_small; first done.

  have hxi : (x < 2 ^ Z.of_nat i)%Z.
  - apply: (Z.lt_le_trans _ _ _ hxn). apply: Z.pow_le_mono_r; lia.

  have hnm : (x < 2 ^ m)%Z.
  - apply: (Z.lt_le_trans _ _ _ hxn). apply: Z.pow_le_mono_r; lia.

  rewrite wunsigned_repr_small; first done.
  by rewrite wbaseE.
Qed.

Lemma wbit_lower_bits_0 x n ws (i : nat) :
  (0 <= Z.of_nat i < n)%Z
  -> (0 <= 2 ^ n * x < wbase ws)%Z
  -> wbit_n (wrepr ws (2 ^ n * x)) i = false.
Proof.
  move=> [h0i hin] hw.
  rewrite wbit_nE.
  rewrite (wunsigned_repr_small hw).
  rewrite -(Zplus_minus (Z.of_nat i) n).
  rewrite Z.pow_add_r; last lia; last lia.
  rewrite -Z.mul_assoc Z.mul_comm.
  rewrite Z_div_mult; last lia.
  rewrite Z_odd_pow_2; first done.
  lia.
Qed.

Lemma worE s (w1 w2 : word s) i :
  wbit_n (wor w1 w2) i = wbit_n w1 i || wbit_n w2 i.
Proof. by rewrite /wbit_n /wor worE. Qed.

Lemma wxorE s (w1 w2: word s) i :
  wbit_n (wxor w1 w2) i = wbit_n w1 i (+) wbit_n w2 i.
Proof. by rewrite /wbit_n /wxor wxorE. Qed.

Lemma wN1E sz i :
  @wbit_n sz (-1)%R i = leq (S i) (wsize_size_minus_1 sz).+1.
Proof. exact: wN1E. Qed.

Lemma wnotE sz (w: word sz) (i: 'I_(wsize_size_minus_1 sz).+1) :
  wbit_n (wnot w) i = ~~ wbit_n w i.
Proof.
  rewrite /wnot wxorE wN1E.
  case: i => i /= ->.
  exact: addbT.
Qed.

Local Ltac lia :=
  rewrite /addn /subn; Lia.lia.

Lemma wshl_sem ws w n :
  (0 <= n)%Z
  -> wshl w n = (wrepr ws (2 ^ n) * w)%R.
Proof.
  move=> hlo.
  apply: wunsigned_inj.

  rewrite -(Z2Nat.id _ hlo).
  rewrite wunsigned_wshl.
  rewrite (Z2Nat.id _ hlo).

  rewrite -(wrepr_unsigned w).
  rewrite -wrepr_mul.
  rewrite !wunsigned_repr.

  rewrite Zmult_mod_idemp_l.
  by rewrite Z.mul_comm.
Qed.

Lemma wshl_ovf sz (w: word sz) c :
  0 <= c →
  (wsize_size_minus_1 sz < Z.to_nat c)%coq_nat →
  wshl w c = 0%R.
Proof.
  move => c_not_neg hc; apply/eqP/eq_from_wbit_n => i.
  rewrite wshlE // {2}/wbit_n wbit0.
  case: i => i /= /leP /le_S_n hi.
  have /leP -> := hi.
  case: leP => //; lia.
Qed.

Lemma msb_wordE {s} (w : word s) : msb w = mathcomp.word.word.msb w.
Proof. by []. Qed.

Lemma wrorE sz (w: word sz) z : wror w z =
   let i := z mod wsize_bits sz in
   wor (wshr w i) (wshl w (wsize_bits sz - i)).
Proof.
  rewrite /wror -wshr_alt -wshl_alt zmod_pow2E.
  rewrite !Nat2Z.inj_succ !Z.pow_succ_r; only 2-4: by lia.
  by rewrite -wsize_size_is_pow2 !Z.mul_assoc wsize_sizeE.
Qed.

Lemma wrolE sz (w: word sz) (z: Z) : wrol w z =
  let i := z mod wsize_bits sz in
  wor (wshl w i) (wshr w (wsize_bits sz - i)).
Proof.
  rewrite /wrol -wshr_alt -wshl_alt zmod_pow2E.
  rewrite !Nat2Z.inj_succ !Z.pow_succ_r; only 2-4: by lia.
  by rewrite -wsize_size_is_pow2 !Z.mul_assoc wsize_sizeE.
Qed.

Lemma wsignedE sz (w: word sz) :
  wsigned w = if msb w then wunsigned w - wbase sz else wunsigned w.
Proof. done. Qed.

Lemma wsigned_repr sz z :
  wmin_signed sz <= z <= wmax_signed sz →
  wsigned (wrepr sz z) = z.
Proof.
  rewrite wsignedE msb_wordE msbE mkword_valK /= wunsigned_repr -/(wbase _) => z_range.
  elim_div => a b [] // ? [] b_range; last by have := wbase_pos sz; lia.
  subst z.
  case: ifP => /ZleP.
  all: move: sz z_range b_range.
  all: move: {-2} Z.mul (erefl Z.mul) => K ?.
  all: rewrite /wmin_signed /wmax_signed /wbase /modulus /two_power_nat.
  all: case => /=; subst K; lia.
Qed.

Lemma wsmulP sz (x y: word sz) :
  let: (hi, lo) := wsmul x y in
  wdwords hi lo = wsigned x * wsigned y.
Proof.
  have x_range := wsigned_range x.
  have y_range := wsigned_range y.
  rewrite /wsmul /wdwords high_bits_wbase.
  set p := _ * wsigned y.
  have p_range : wmin_signed sz * wmax_signed sz <= p <= wmin_signed sz * wmin_signed sz.
  { subst p; case: sz x y x_range y_range => x y;
    rewrite /wmin_signed /wmax_signed /=;
    nia. }
  have hi_range : wmin_signed sz <= p / wbase sz <= wmax_signed sz.
  { move: sz {x y x_range y_range} p p_range => sz p p_range.
    elim_div => a b [] // ? [] b_range; last by have := wbase_pos sz; lia.
    subst p.
    move: sz p_range b_range.
    move: {-2} Z.mul (erefl Z.mul) => K ?.
    rewrite /wmin_signed /wmax_signed /wbase /modulus /two_power_nat.
    case => /=; subst K; lia. }
  rewrite wsigned_repr; last exact: hi_range.
  rewrite wunsigned_repr -/(wbase _).
  have := Z_div_mod_eq_full p (wbase sz).
  lia.
Qed.

Lemma msb0 sz : @msb sz 0 = false.
Proof. by case: sz. Qed.

Lemma wshr0 sz (w: word sz) : wshr w 0 = w.
Proof. by rewrite /wshr Z.shiftr_0_r ureprK. Qed.

Lemma wshr_full sz (w : word sz) : wshr w (wsize_bits sz) = 0%R.
Proof.
  apply/eqP; rewrite word_eqE; apply/eqP.
  rewrite wsize_bitsE Zpos_P_of_succ_nat -Nat2Z.inj_succ.
  rewrite -!/(wunsigned _) wunsigned_wshr wunsigned0.
  rewrite -two_power_nat_equiv.
  exact: Z.div_small (wunsigned_range w).
Qed.

Lemma wshl0 sz (w: word sz) : wshl w 0 = w.
Proof. by rewrite /wshl /lsl Z.shiftl_0_r ureprK. Qed.

Lemma wshl_full sz (w : word sz) : wshl w (wsize_bits sz) = 0%R.
Proof.
  apply/eqP/eq_from_wbit_n.
  move=> i.
  rewrite wshlE; last by [].
  rewrite wsize_bitsE /=.
  rewrite SuccNat2Pos.id_succ.
  case hi: (_ <= _ <= _)%N; last by rewrite w0E.
  by move: hi => /andP [] /ltn_geF ->.
Qed.

Lemma wsar0 sz (w: word sz) : wsar w 0 = w.
Proof. by rewrite /wsar /asr Z.shiftr_0_r sreprK. Qed.

Lemma zero_extend0 sz sz' :
  @zero_extend sz sz' 0%R = 0%R.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma zero_extend_sign_extend sz sz' s (w: word s) :
 (sz ≤ sz')%CMP →
  zero_extend sz (sign_extend sz' w) = sign_extend sz w.
Proof.
move => hsz; apply: wunsigned_inj.
rewrite !wunsigned_repr /=.
case: (modulus_m (wsize_size_m hsz)) => n hn.
by rewrite hn mod_pq_mod_q.
Qed.

Lemma zero_extend_cut (s1 s2 s3: wsize) (w: word s3) :
  (s3 ≤ s2)%CMP →
  zero_extend s1 (zero_extend s2 w) = zero_extend s1 w.
Proof.
  move => /wbase_m hle.
  rewrite /zero_extend wunsigned_repr_small //.
  have := wunsigned_range w.
  lia.
Qed.

Lemma wbit_zero_extend s s' (w: word s') i :
  wbit_n (zero_extend s w) i = (i <= wsize_size_minus_1 s)%nat && wbit_n w i.
Proof.
rewrite /zero_extend /wbit_n /wunsigned /wrepr.
move: (urepr w) => {w} z.
rewrite mkwordK.
set m := wsize_size_minus_1 _.
rewrite !wbit_spec.
rewrite /modulus two_power_nat_equiv.
case: leP => hi.
+ rewrite Z.mod_pow2_bits_low //; lia.
rewrite Z.mod_pow2_bits_high //; lia.
Qed.

Lemma zero_extend1 sz sz' :
  @zero_extend sz sz' 1%R = 1%R.
Proof.
  apply/eqP/eq_from_wbit => -[i hi].
  have := @wbit_zero_extend sz sz' 1%R i.
  by rewrite /wbit_n => ->; rewrite -ltnS hi.
Qed.

Lemma sign_extend_truncate s s' (w: word s') :
  (s ≤ s')%CMP →
  sign_extend s w = zero_extend s w.
Proof.
  rewrite /sign_extend /zero_extend /wsigned /wunsigned sreprE /= /wrepr.
  move: (urepr w) => z hle.
  apply: wunsigned_inj; rewrite /wunsigned !mkwordK.
  have [n ->] := modulus_m (wsize_size_m hle).
  case: word_ssrZ.ltzP => // hgt.
  by rewrite Zminus_mod Z_mod_mult Z.sub_0_r Zmod_mod.
Qed.

Lemma sign_extend_u sz (w: word sz) : sign_extend sz w = w.
Proof. exact: sreprK. Qed.

Lemma truncate_word_errP s1 s2 (w: word s2) e :
  truncate_word s1 w = Error e → e = ErrType ∧ (s2 < s1)%CMP.
Proof. by case: truncate_wordP' => // -> [] <-. Qed.

Lemma wbase_n0 sz : wbase sz <> 0%Z.
Proof. by case sz. Qed.

Lemma wsigned0 sz : @wsigned sz 0%R = 0%Z.
Proof. by case: sz. Qed.

Lemma wsigned1 sz : @wsigned sz 1%R = 1%Z.
Proof. by case: sz. Qed.

Lemma wsignedN1 sz : @wsigned sz (-1)%R = (-1)%Z.
Proof. by case: sz. Qed.

Lemma sign_extend0 sz sz' :
  @sign_extend sz sz' 0%R = 0%R.
Proof. by rewrite /sign_extend wsigned0 wrepr0. Qed.

Lemma wandC sz : commutative (@wand sz).
Proof.
  by move => x y; apply/eqP/eq_from_wbit => i;
  rewrite /wand !mathcomp.word.word.wandE andbC.
Qed.

Lemma wandA sz : associative (@wand sz).
Proof.
  by move => x y z; apply/eqP/eq_from_wbit_n => i;
  rewrite !wandE andbA.
Qed.

Lemma wand0 sz (x: word sz) : wand 0 x = 0%R.
Proof. by apply/eqP. Qed.

Lemma wand_xx sz (x: word sz) : wand x x = x.
Proof. by apply/eqP/eq_from_wbit; rewrite /= Z.land_diag. Qed.

Lemma wandN1 sz (x: word sz) : wand (-1) x = x.
Proof.
  apply/eqP/eq_from_wbit_n => i.
  by rewrite wandE wN1E ltn_ord.
Qed.

Lemma wand_small n :
  (0 <= n < wbase U16)
  -> wand (wrepr U32 n) (zero_extend U32 (wrepr U16 (-1))) = wrepr U32 n.
Proof.
  move=> [hlo hhi].
  apply/eqP/eq_from_wbit_n.
  move=> [i hrangei] /=.

  case hi: (i < 16)%nat.

  - rewrite wandE.
    rewrite wrepr_m1 wbit_zero_extend.
    rewrite wN1E.

    have -> : (i <= wsize_size_minus_1 U32)%nat.
    - by apply: (ltnSE hrangei).
    rewrite andTb.

    rewrite hi.
    by rewrite andbT.

  have -> : wbit_n (wrepr U32 n) i = false.
  - rewrite -(Nat2Z.id i).
    apply: (wbit_higher_bits_0 (n := 16) _ _) => //=.
    move: hi => /ZNltP hi.
    move: hrangei => /ZNleP /= h.
    lia.

  rewrite wandE.
  rewrite wrepr_m1 wbit_zero_extend.
  rewrite wN1E.
  rewrite hi /=.
  by rewrite !andbF.
Qed.

Lemma worC sz : commutative (@wor sz).
Proof.
  by move => x y; apply/eqP/eq_from_wbit => i;
  rewrite /wor !mathcomp.word.word.worE orbC.
Qed.

Lemma wor0 sz (x: word sz) : wor 0 x = x.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma wor_xx sz (x: word sz) : wor x x = x.
Proof. by apply/eqP/eq_from_wbit; rewrite /= Z.lor_diag. Qed.

Lemma wxor0 sz (x: word sz) : wxor 0 x = x.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma wxor_xx sz (x: word sz) : wxor x x = 0%R.
Proof. by apply/eqP/eq_from_wbit; rewrite /= Z.lxor_nilpotent. Qed.

Lemma wmulE sz (x y: word sz) : (x * y)%R = wrepr sz (wunsigned x * wunsigned y).
Proof. by rewrite wrepr_mul !wrepr_unsigned. Qed.

Lemma wror0 sz (w : word sz) : wror w 0 = w.
Proof.
  rewrite wrorE /= wshr0 wshl_full.
  by rewrite worC wor0.
Qed.

Lemma wrol0 sz (w : word sz) : wrol w 0 = w.
Proof.
  rewrite wrolE /= wshl0 wshr_full.
  by rewrite worC wor0.
Qed.

Lemma wadd_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  zero_extend sz (x + y) = (zero_extend sz x + zero_extend sz y)%R.
Proof.
move => hle; apply: wunsigned_inj.
rewrite {1}/zero_extend wunsigned_repr /wunsigned !addwE.
rewrite !mkwordK -Zplus_mod.
case: (modulus_m (wsize_size_m hle)) => n -> {hle}.
by rewrite mod_pq_mod_q.
Qed.

Lemma wmul_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  zero_extend sz (x * y) = (zero_extend sz x * zero_extend sz y)%R.
Proof.
move => hle; apply: wunsigned_inj.
rewrite /zero_extend !wunsigned_repr !mkwordK.
rewrite /wunsigned /urepr /= -Zmult_mod.
case: (modulus_m (wsize_size_m hle)) => n -> {hle}.
by rewrite mod_pq_mod_q.
Qed.

Lemma zero_extend_m1 sz sz' :
  (sz ≤ sz')%CMP →
  @zero_extend sz sz' (-1) = (-1)%R.
Proof. exact: zero_extend_wrepr. Qed.

Lemma wopp_zero_extend sz sz' (x: word sz') :
  (sz ≤ sz')%CMP →
  zero_extend sz (-x) = (- zero_extend sz x)%R.
Proof.
 by move=> hsz; rewrite -(mulN1r x) wmul_zero_extend // zero_extend_m1 // mulN1r.
Qed.

Lemma wsub_zero_extend sz sz' (x y : word sz'):
  (sz ≤ sz')%CMP →
  zero_extend sz (x - y) = (zero_extend sz x - zero_extend sz y)%R.
Proof.
  by move=> hsz; rewrite wadd_zero_extend // wopp_zero_extend.
Qed.

Lemma zero_extend_wshl sz sz' (x: word sz') c :
  (sz ≤ sz')%CMP →
  0 <= c →
  zero_extend sz (wshl x c) = wshl (zero_extend sz x) c.
Proof.
move => hle hc; apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wshlE) //.
have := wsize_size_m hle.
move: i.
set m := wsize_size_minus_1 _.
set m' := wsize_size_minus_1 _.
case => i /= /leP hi hm.
have him : (i <= m)%nat by apply/leP; lia.
rewrite him andbT /=.
have him' : (i <= m')%nat by apply/leP; lia.
rewrite him' andbT.
case: leP => //= hci.
have -> // : (i - Z.to_nat c <= m)%nat.
apply/leP; lia.
Qed.

Lemma wand_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  wand (zero_extend sz x) (zero_extend sz y) = zero_extend sz (wand x y).
Proof.
move => hle.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wandE).
by case: (_ <= _)%nat.
Qed.

Lemma wor_zero_extend sz sz' (x y : word sz') :
  (sz <= sz')%CMP
  -> wor (zero_extend sz x) (zero_extend sz y) = zero_extend sz (wor x y).
Proof.
  move=> hws.
  apply/eqP.
  apply/eq_from_wbit_n.
  move=> i.
  rewrite !(wbit_zero_extend, worE).
  by case: (_ <= _)%nat.
Qed.

Lemma wxor_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  wxor (zero_extend sz x) (zero_extend sz y) = zero_extend sz (wxor x y).
Proof.
move => hle.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wxorE).
by case: (_ <= _)%nat.
Qed.

Lemma wnot_zero_extend sz sz' (x : word sz') :
  (sz ≤ sz')%CMP →
  wnot (zero_extend sz x) = zero_extend sz (wnot x).
Proof.
move => hle.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wnotE).
have := wsize_size_m hle.
move: i.
set m := wsize_size_minus_1 _.
set m' := wsize_size_minus_1 _.
case => i /= /leP hi hm.
have him : (i <= m)%nat. by apply/leP; lia.
rewrite him /=.
have hi' : (i < m'.+1)%nat. apply /ltP. lia.
by have /= -> := @wnotE sz' x (Ordinal hi') .
Qed.

Lemma wleuE sz (w1 w2: word sz) :
 (wunsigned (w2 - w1) == (wunsigned w2 - wunsigned w1))%Z = wle Unsigned w1 w2.
Proof. by rewrite /= lezE leNgt wltuE negbK. Qed.

Lemma wleuE' sz (w1 w2 : word sz) :
  (wunsigned (w1 - w2) != (wunsigned w1 - wunsigned w2)%Z) || (w1 == w2)
  = wle Unsigned w1 w2.
Proof. by rewrite -wltuE /= lezE le_eqVlt orbC. Qed.

Lemma wltsE_aux sz (α β: word sz) : α ≠ β →
  wlt Signed α β = (msb (α - β) != (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof.
Local Opaque GRing.add.
move=> ne_ab; rewrite /= !msb_wordE /wsigned /srepr ltzE.
rewrite !mathcomp.word.word.msbE /= !subZE; set w := (_ sz);
  case: (lerP (modulus _) (val α)) => ha;
  case: (lerP (modulus _) (val β)) => hb;
  case: (lerP (modulus _) (val _)) => hab.
+ rewrite ltrD2r eq_sym eqb_id negbK opprB !addrA subrK.
  rewrite [val (α - β)%R]subw_modE /urepr /= -/w.
  case: ltrP; first by rewrite addrK eqxx.
  by rewrite addr0 lt_eqF // ltrBlDr ltrDl modulus_gt0.
+ rewrite ltrD2r opprB !addrA subrK eq_sym eqbF_neg negbK.
  rewrite [val (α - β)%R]subw_modE /urepr -/w /=; case: ltrP.
  + by rewrite mulr1n gt_eqF // ltrDl modulus_gt0.
  + by rewrite addr0 eqxx.
+ rewrite ltrBlDr (lt_le_trans (urepr_ltmod _)); last first.
    by rewrite lerDr urepr_ge0.
  rewrite eq_sym eqb_id negbK; apply/esym.
  rewrite [val _]subw_modE /urepr -/w /= ltNge ltW /=.
  * by rewrite addr0 addrAC eqxx.
  * by rewrite (lt_le_trans hb).
+ rewrite ltrBlDr (lt_le_trans (urepr_ltmod _)); last first.
    by rewrite lerDr urepr_ge0.
  rewrite eq_sym eqbF_neg negbK [val _]subw_modE /urepr -/w /=.
  rewrite ltNge ltW ?addr0; last first.
    by rewrite (lt_le_trans hb).
  by rewrite addrAC gt_eqF // ltrBlDr ltrDl modulus_gt0.
+ rewrite ltrBrDl ltNge ltW /=; last first.
    by rewrite (lt_le_trans (urepr_ltmod _)) // lerDl urepr_ge0.
  apply/esym/negbTE; rewrite negbK; apply/eqP/esym.
  rewrite [val _]subw_modE /urepr /= -/w; have ->/=: (val α < val β)%R.
  by have := ltr_leD ha hb; rewrite addrC ltrD2l.
  rewrite mulr1n addrK opprD addrA lt_eqF //= opprK.
  by rewrite ltrDl modulus_gt0.
+ rewrite ltrBrDl ltNge ltW /=; last first.
    by rewrite (lt_le_trans (urepr_ltmod _)) // lerDl urepr_ge0.
  apply/esym/negbTE; rewrite negbK eq_sym eqbF_neg negbK.
  rewrite [val _]subw_modE /urepr -/w /= opprD addrA opprK.
  by have ->//: (val α < val β)%R; apply/(lt_le_trans ha).
+ rewrite [val (α - β)%R](subw_modE α β) -/w /urepr /=.
  rewrite eq_sym eqb_id negbK; case: ltrP.
  * by rewrite mulr1n addrK eqxx.
  * by rewrite addr0 lt_eqF // ltrBlDr ltrDl modulus_gt0.
+ rewrite [val (α - β)%R](subw_modE α β) -/w /urepr /=.
  rewrite eq_sym eqbF_neg negbK; case: ltrP.
  * by rewrite mulr1n gt_eqF // ltrDl modulus_gt0.
  * by rewrite addr0 eqxx.
Local Transparent GRing.add.
Qed.

Section WCMPE.

#[local]
Notation wle_msb x y :=
  (msb (x - y) == (wsigned (x - y) != (wsigned x - wsigned y)%Z))
  (only parsing, x in scope ring_scope, y in scope ring_scope).

#[local]
Notation wlt_msb x y := (~~ wle_msb x y) (only parsing).

Lemma wltsE ws (x y : word ws) :
  wlt_msb x y = wlt Signed x y.
Proof.
  case: (x =P y) => [<- | ?]; last by rewrite wltsE_aux.
  by rewrite /= ltzE ltxx GRing.subrr Z.sub_diag wsigned0 msb0.
Qed.

Lemma wlesE ws (x y : word ws) :
  wle_msb x y = wle Signed y x.
Proof. by rewrite -[_ == _]negbK wltsE /= lezE leNgt. Qed.

Lemma wltsE' ws (x y : word ws):
  ((x != y) && wle_msb x y) = wlt Signed y x.
Proof.
  by rewrite wlesE /= ltzE lt_def eqtype.inj_eq; last exact: word.srepr_inj.
Qed.

Lemma wlesE' ws (x y : word ws) :
  ((x == y) || wlt_msb x y) = wle Signed x y.
Proof. by rewrite -[_ || _]negbK negb_or negbK wltsE' /= lezE leNgt. Qed.

End WCMPE.

Lemma wdwordu0 sz (w:word sz) : wdwordu 0 w = wunsigned w.
Proof. done. Qed.

Lemma wdwords0 sz (w:word sz) :
  wdwords (if msb w then (-1)%R else 0%R) w = wsigned w.
Proof.
  rewrite wsignedE /wdwords; case: msb; rewrite ?wsigned0 ?wsignedN1; ring.
Qed.

Lemma lsr0 n (w: n.-word) : lsr w 0 = w.
Proof. by apply/word_eqP; rewrite -urepr_word urepr_lsr. Qed.

Lemma subword0 (ws ws' :wsize) (w: word ws') :
   mathcomp.word.word.subword 0 ws w = zero_extend ws w.
Proof. by rewrite /subword -urepr_word urepr_lsr Z.shiftr_0_r. Qed.

Lemma wpbroadcast0 ve sz :
  @wpbroadcast ve sz 0%R = 0%R.
Proof.
  rewrite /wpbroadcast/make_vec.
  suff -> : wcat_r (nseq _ 0%R) = 0.
  - by rewrite wrepr0.
  by move => q; elim => // n /= ->; rewrite Z.shiftl_0_l.
Qed.

(* Test case from the documentation: VPMADDWD wraps when all inputs are min-signed *)
Local Lemma test_wpmaddwd_wraps :
  let: s16 := wrepr U16 (wmin_signed U16) in
  let: s32 := make_vec U32 [:: s16 ; s16 ] in
  let: res := wpmaddwd s32 s32 in
  let: expected := wrepr U32 (wmin_signed U32) in
  res = expected.
Proof. vm_compute. by apply/eqP. Qed.

Lemma wror_opp sz (x: word sz) c :
  wror x (wsize_bits sz - c) = wrol x c.
Proof.
  rewrite wrorE wrolE.
  have : 0 < wsize_bits sz by [].
  move: (wsize_bits _) (wshr_full x) (wshl_full x) => n R L n_pos.
  have nnz : n ≠ 0 by lia.
  rewrite Zminus_mod Z_mod_same_full Z.sub_0_l.
  have : c mod n = 0 ∨ 0 < c mod n < n.
  - move: (Z.mod_pos_bound c n n_pos); lia.
  case => c_mod_n /=.
  - by rewrite c_mod_n Z.sub_0_r Zmod_0_l wshr0 wshl0 R L.
  rewrite !Z.mod_opp_l_nz // Zmod_mod; last lia.
  rewrite worC; do 2 f_equal.
  lia.
Qed.

Lemma wror_m sz (x: word sz) y y' :
  y mod wsize_bits sz = y' mod wsize_bits sz →
  wror x y = wror x y'.
Proof. by rewrite !wrorE => ->. Qed.

Lemma word_uincl_eq s (w w': word s):
  word_uincl w w' → w = w'.
Proof. by move=> /andP [] _ /eqP; rewrite zero_extend_u. Qed.

Lemma word_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP -> word_uincl (zero_extend sz w') w'.
Proof. by move=> ?;apply /andP. Qed.

Lemma word_uincl_zero_extR sz sz' (w: word sz) :
  (sz ≤ sz')%CMP →
  word_uincl w (zero_extend sz' w).
Proof.
  move => hle; apply /andP; split; first exact: hle.
  by rewrite zero_extend_idem // zero_extend_u.
Qed.

Lemma truncate_word_uincl sz1 sz2 w1 (w2: word sz2) :
  truncate_word sz1 w2 = ok w1 → word_uincl w1 w2.
Proof. by move=> /truncate_wordP[? ->]; exact: word_uincl_zero_ext. Qed.

Lemma ZlnotE (x : Z) :
  Z.lnot x = (- (x + 1))%Z.
Proof. have := Z.add_lnot_diag x. lia. Qed.

Lemma Zlxor_mod (a b n : Z) :
  (0 <= n)%Z
  -> ((Z.lxor a b) mod 2^n)%Z = (Z.lxor (a mod 2^n) (b mod 2^n))%Z.
Proof.
  move=> hn.
  apply: Z.bits_inj'.
  move=> i _.
  rewrite Z.lxor_spec.

  case: (Z.lt_ge_cases i n) => [hlt | hge].
  - rewrite 3!(Z.mod_pow2_bits_low _ _ _ hlt). exact: Z.lxor_spec.

  have hrange: (0 <= n <= i)%Z.
  - by split.
  by rewrite 3!(Z.mod_pow2_bits_high _ _ _ hrange).
Qed.

Lemma wrepr_xor ws (x y : Z) :
  wxor (wrepr ws x) (wrepr ws y) = wrepr ws (Z.lxor x y).
Proof.
  apply: wunsigned_inj.
  rewrite wunsigned_repr /wunsigned urepr_wxor !mkwordK.
  set wsz := (wsize_size_minus_1 ws).+1.
  change (word.modulus wsz) with (two_power_nat wsz).
  rewrite two_power_nat_equiv.
  by rewrite Zlxor_mod.
Qed.

Lemma wxorA ws : associative (@wxor ws).
Proof.
  move=> x y z.
  rewrite -(wrepr_unsigned x) -(wrepr_unsigned y) -(wrepr_unsigned z).
  by rewrite !wrepr_xor Z.lxor_assoc.
Qed.

Lemma wxorC ws : commutative (@wxor ws).
Proof.
  move=> x y.
  rewrite -(wrepr_unsigned x) -(wrepr_unsigned y).
  by rewrite !wrepr_xor Z.lxor_comm.
Qed.

Lemma wrepr_wnot ws z :
  wnot (wrepr ws z) = wrepr ws (Z.lnot z).
Proof. by rewrite /wnot wrepr_xor Z.lxor_m1_r. Qed.

Lemma wnot_wnot ws (x : word ws) :
  wnot (wnot x) = x.
Proof. by rewrite -(wrepr_unsigned x) 2!wrepr_wnot Z.lnot_involutive. Qed.

Lemma wnotP ws (x : word ws) :
  wnot x = wrepr ws (Z.lnot (wunsigned x)).
Proof. by rewrite -{1}(wrepr_unsigned x) wrepr_wnot. Qed.

Lemma msb_wnot ws (x : word ws) :
  msb (wnot x) = ~~ msb x.
Proof. rewrite /msb. by have /= -> := wnotE x (Ordinal (ltnSn _)). Qed.

Lemma wnot1_wopp ws (x : word ws) :
  (wnot x + 1)%R = (- x)%R.
Proof.
  rewrite wnotP.
  rewrite wrepr_add.
  rewrite wrepr_opp.
  rewrite wrepr_unsigned.
  rewrite wrepr_m1.
  exact: GRing.Theory.addrNK.
Qed.

Lemma wsub_wnot1 ws (x y : word ws) :
  (x + wnot y + 1)%R = (x - y)%R .
Proof. by rewrite -GRing.Theory.addrA wnot1_wopp. Qed.

Lemma wunsigned_wnot ws (x : word ws) :
  wunsigned (wnot x) = (wbase ws - wunsigned x - 1)%Z.
Proof.
  rewrite wnotP wunsigned_repr.
  change (word.modulus (wsize_size_minus_1 ws).+1) with (wbase ws).
  rewrite ZlnotE.
  rewrite -(Z.mod_add _ 1 _); last exact: wbase_n0.
  rewrite Zmod_small; first lia.
  have := wunsigned_range x.
  lia.
Qed.

Lemma wsigned_wnot ws (x : word ws) :
  (wsigned (wnot x))%Z = (- wsigned x - 1)%Z.
Proof.
  rewrite 2!wsignedE.
  rewrite msb_wnot.
  case: msb => /=;
    rewrite wunsigned_wnot;
    lia.
Qed.

Lemma wsigned_wsub_wnot1 ws (x y : word ws) :
  (wsigned x + wsigned (wnot y) + 1)%Z = (wsigned x - wsigned y)%Z.
Proof. rewrite -Z.add_assoc wsigned_wnot. lia. Qed.

Lemma unsigned_overflow sz (z: Z):
  (0 <= z)%Z ->
  (wunsigned (wrepr sz z) != z) = (wbase sz <=? z)%Z.
Proof.
  move => hz.
  rewrite wunsigned_repr; apply/idP/idP.
  * apply: contraR => /negbTE /Z.leb_gt lt; apply/eqP.
      by rewrite Z.mod_small //; lia.
  * apply: contraL => /eqP <-; apply/negbT/Z.leb_gt.
    by case: (Z_mod_lt z (wbase sz)).
Qed.

Lemma add_overflow sz (w1 w2: word sz) :
  (wbase sz <=? wunsigned w1 + wunsigned w2)%Z =
  (wunsigned (w1 + w2) != (wunsigned w1 + wunsigned w2)%Z).
Proof.
  rewrite unsigned_overflow //; rewrite -!/(wunsigned _).
  have := wunsigned_range w1; have := wunsigned_range w2.
  lia.
Qed.

Lemma wbit_pow_2 ws n x (i : nat) :
  0 <= n
  -> (Z.to_nat n <= i <= wsize_size_minus_1 ws)%nat
  -> wbit_n (wrepr ws (2 ^ n * x)) i = wbit_n (wrepr ws x) (i - Z.to_nat n).
Proof.
  move=> h0n hrange.
  rewrite wrepr_mul.
  rewrite -(wshl_sem _ h0n).
  rewrite wshlE //.
  by rewrite hrange.
Qed.

Lemma subword_make_vec_bits_low (n m : nat) x y :
  (Z.of_nat n < Z.of_nat m)%Z ->
  word.subword 0 n (word.mkword m (wcat_r [:: x; y ])) = x.
Proof.
  move=> h.
  apply/eqP/word.eq_from_wbit => i.
  rewrite subwordE wbit_t2wE mkword_valK /=.
  rewrite (nth_map i); last by rewrite size_enum_ord.
  rewrite !wbit_spec addn0 nth_ord_enum modulusZE.
  rewrite Z.shiftl_0_l Z.lor_0_r.
  rewrite Z.mod_pow2_bits_low.
  - rewrite Z.lor_spec Z.shiftl_spec_low; first by rewrite orbF.
    by apply/ZNltP.
  apply: (Z.lt_trans _ _ _ _ h).
  by apply/ZNltP.
Qed.

Lemma Z_lor_le x y ws :
  (0 <= x < wbase ws)%Z ->
  (0 <= y < wbase ws)%Z ->
  (0 <= Z.lor x y < wbase ws)%Z.
Proof.
  move=> /iswordZP hx /iswordZP hy.
  rewrite -[x]/(urepr (mkWord hx)) -[y]/(urepr (mkWord hy)).
  apply/iswordZP.
  exact: word.wor_subproof.
Qed.

Lemma make_vec_4x64 (w : word.word U64) :
  make_vec U256 [:: make_vec U128 [:: w; w ]; make_vec U128 [:: w; w ]]
  = make_vec U256 [:: w; w; w; w ].
Proof.
  rewrite /make_vec /wcat_r.
  rewrite !Z.shiftl_0_l !Z.lor_0_r.
  f_equal.
  rewrite Z.shiftl_lor.
  rewrite Z.lor_assoc.
  rewrite Z.shiftl_shiftl; last done.
  rewrite -![urepr _]/(wunsigned _).
  rewrite wunsigned_repr_small; first done.

  have [hw0 hwn] := wunsigned_range w.

  apply: Z_lor_le.
  - have := @wbase_m U64 U128 refl_equal. lia.

  rewrite Z.shiftl_mul_pow2; last done.
  split; first lia.
  move: hwn; rewrite !wbaseE /=.
  change (Z.pow_pos 2 128) with (Z.pow_pos 2 64 * Z.pow_pos 2 64).
  lia.
Qed.

Lemma wrepr_int_of_word sz si (w:word sz) : wrepr sz (int_of_word si w) = w.
Proof. case: si => /=; auto using wrepr_signed, wrepr_unsigned. Qed.

Lemma wint_of_intP si sz i w : wint_of_int si sz i = ok w -> w = wrepr sz i /\ in_wint_range si sz i = ok tt.
Proof. by rewrite /wint_of_int; t_xrbindP => ? <-. Qed.

Lemma wint_of_int_wrepr si sz i w : wint_of_int si sz i = ok w -> w = wrepr sz i.
Proof. by move=> /wint_of_intP []. Qed.

Lemma int_of_word_eqb si sz (w1 w2 : word sz) :
  (int_of_word si w1 =? int_of_word si w2)%Z = (w1 == w2).
Proof.
  apply Bool.eq_iff_eq_true; rewrite /int_of_word; split.
  + move=> /word_ssrZ.ZeqbP => h; apply/eqP.
    case: si h => /= h.
    + by rewrite -(wrepr_signed w1) -(wrepr_signed w2) h.
    by rewrite -(wrepr_unsigned w1) -(wrepr_unsigned w2) h.
  by move=> /eqP ->; apply Z.eqb_refl.
Qed.

Lemma Z_rem_bound (a b : Z) : (b <> 0 -> - Z.abs b < Z.rem a b < Z.abs b)%Z.
Proof.
  move=> hb.
  case: (ZleP 0 a) => ha.
  + by have := Zquot.Zrem_lt_pos a b ha hb; Lia.lia.
  rewrite -(Z.opp_involutive a) Zquot.Zrem_opp_l.
  have := Zquot.Zrem_lt_pos (-a) b _ hb; Lia.lia.
Qed.

Lemma Z_quot_bound (B a b : Z) :
  (0 < B ->
   -B <= a <= B - 1 ->
   -B <= b <= B - 1 ->
   b <> 0 ->
   ~(a = -B /\ b = -1) ->
   -B <= Z.quot a b <= B - 1)%Z.
Proof.
  move=> hB ha hb hab.
  case: (ZltP 0 b) => ?.
  + split.
    + by apply Z.quot_le_lower_bound => //; Lia.nia.
    by apply Z.quot_le_upper_bound => //; Lia.nia.
  rewrite -(Z.opp_involutive b).
  rewrite Zquot.Zquot_opp_r; split; rewrite Z.opp_le_mono Z.opp_involutive.
  + apply: Z.quot_le_upper_bound; Lia.nia.
  apply Z.quot_le_lower_bound; Lia.nia.
Qed.
