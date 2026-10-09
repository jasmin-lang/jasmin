(* ** Machine word *)

(* ** Imports and settings *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype choice tuple.
From mathcomp Require Import div fintype order ssralg ssrnum word_ssrZ word.
From Coq Require Zquot.
From Coq Require Import ZArith.
Require Import utils.
Require Export wsize.
Import Utf8 Lia.
Import word_ssrZ.

Import GRing.Theory Num.Theory Order.POrderTheory Order.TotalTheory.
Import ssrnat.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Local Open Scope Z_scope.

(* -------------------------------------------------------------- *)
Ltac elim_div :=
   unfold Z.div, Z.modulo;
     match goal with
       |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
       |  |-  context[ Z.div_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
     end; unfold Remainder.

Lemma mod_pq_mod_q x p q :
  0 < p → 0 < q →
  (x mod (p * q)) mod q = x mod q.
Proof.
move => hzp hzq.
have hq : q ≠ 0 by nia.
have hpq : p * q ≠ 0 by nia.
elim_div => z z0 /(_ hq); elim_div => z1 z2 /(_ hpq) => [] [?] hr1 [?] hr2; subst.
elim_div => z2 z3 /(_ hq) [heq hr3].
intuition (try nia).
suff : p * z1 + z = z2; nia.
Qed.

Lemma modulus_m a b :
  a ≤ b →
  ∃ n, modulus b.+1 = modulus n * modulus a.+1.
Proof.
move => hle.
exists (b - a)%nat; rewrite /modulus !two_power_nat_equiv -Z.pow_add_r; try lia.
rewrite (Nat2Z.inj_sub _ _ hle); f_equal; lia.
Qed.

(* -------------------------------------------------------------- *)
Definition nat7   : nat := 7.
Definition nat15  : nat := nat7.+4.+4.
Definition nat31  : nat := nat15.+4.+4.+4.+4.
Definition nat63  : nat := nat31.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat127 : nat := nat63.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat255 : nat := nat127.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.

Definition wsize_size_minus_1 (s: wsize) : nat :=
  match s with
  | U8   => nat7
  | U16  => nat15
  | U32  => nat31
  | U64  => nat63
  | U128 => nat127
  | U256 => nat255
  end.

Coercion nat_of_wsize (sz : wsize) :=
  (wsize_size_minus_1 sz).+1.

Definition wsize_bits (sz: wsize) : Z :=
  Zpos match sz return positive with
  | U8   => 8
  | U16  => 16
  | U32  => 32
  | U64  => 64
  | U128 => 128
  | U256 => 256
  end.

Lemma wsize_bitsE s :
  wsize_bits s = Zpos (Pos.of_succ_nat (wsize_size_minus_1 s)).
Proof. by case: s. Qed.

Definition wsize_log2 sz : nat :=
  match sz with
  | U8 => 0
  | U16 => 1
  | U32 => 2
  | U64 => 3
  | U128 => 4
  | U256 => 5
  end.

Lemma wsize8 : wsize_size U8 = 1%Z.
Proof. done. Qed.

Definition wbase (s: wsize) : Z :=
  modulus (wsize_size_minus_1 s).+1.

Lemma wbaseE ws :
  wbase ws = 2 ^ Z.of_nat (wsize_size_minus_1 ws).+1.
Proof. by rewrite /wbase /word.modulus two_power_nat_equiv. Qed.

Lemma le0_wsize_size ws : 0 <= wsize_size ws.
Proof. rewrite /wsize_size; lia. Qed.
Arguments le0_wsize_size {ws}.
#[global]
Hint Resolve le0_wsize_size : core.

Lemma wsize_size_is_pow2 sz :
  wsize_size sz = 2 ^ Z.of_nat (wsize_log2 sz).
Proof. by case: sz. Qed.

Lemma wsize_bits_wbase sz : 2 ^ wsize_bits sz = wbase sz.
Proof. by case: sz. Qed.

Lemma log2_wsize_bits sz x :
  0 <= x < wbase sz →
  Z.log2 x < wsize_bits sz.
Proof.
  case => /Z.le_lteq[]; last by move => <-; clear; case: sz.
  by move => h0; rewrite -Z.log2_lt_pow2 // wsize_bitsE -wbaseE.
Qed.

Lemma wsize_size_pos sz :
  0 < wsize_size sz.
Proof. done. Qed.

Lemma wsize_size_wbase s : wsize_size s < wbase U8.
Proof. by apply /ZltP; case: s; vm_compute. Qed.

Lemma wsize_size_div_wbase sz sz' : (wsize_size sz | wbase sz').
Proof.
  apply Znumtheory.Zmod_divide => //.
  by case sz; case sz'.
Qed.

Lemma mod_wbase_wsize_size z sz sz' :
  z mod wbase sz mod wsize_size sz' = z mod wsize_size sz'.
Proof. by rewrite -Znumtheory.Zmod_div_mod //; apply wsize_size_div_wbase. Qed.

Lemma wsize_cmpP sz sz' :
  wsize_cmp sz sz' = Nat.compare (wsize_size_minus_1 sz) (wsize_size_minus_1 sz').
Proof. by case: sz sz' => -[]; vm_compute. Qed.

Lemma wsize_size_m s s' :
  (s ≤ s')%CMP →
  wsize_size_minus_1 s ≤ wsize_size_minus_1 s'.
Proof.
by move=> /eqP; rewrite /cmp_le /gcmp wsize_cmpP Nat.compare_ge_iff.
Qed.

Lemma wbase_m s s' :
  (s ≤ s')%CMP →
  wbase s <= wbase s'.
Proof.
  rewrite /wbase /modulus !two_power_nat_S !two_power_nat_equiv => /wsize_size_m s_le_s'.
  apply: Z.mul_le_mono_nonneg_l; first by [].
  apply: Z.pow_le_mono_r; first by [].
  lia.
Qed.

Lemma wsize_size_le a b :
  (a ≤ b)%CMP →
  (wsize_size a | wsize_size b).
Proof.
  case: a; case: b => // _.
  1, 7, 12, 16, 19, 21: by exists 1.
  1, 6, 10, 13, 15: by exists 2.
  1, 5, 8, 10: by exists 4.
  1, 4, 6: by exists 8.
  1, 3: by exists 16.
  by exists 32.
Qed.

Coercion nat_of_pelem (pe: pelem) : nat :=
  match pe with
  | PE1 => 1
  | PE2 => 2
  | PE4 => 4
  | PE8 => nat_of_wsize U8
  | PE16 => nat_of_wsize U16
  | PE32 => nat_of_wsize U32
  | PE64 => nat_of_wsize U64
  | PE128 => nat_of_wsize U128
  end.

Definition word sz : Type := (wsize_size_minus_1 sz).+1.-word.
HB.instance Definition _ sz := Equality.on (word sz).
HB.instance Definition _ sz := GRing.ComNzRing.on (word sz).
Bind Scope ring_scope with word.

Global Opaque word.

Definition winit (ws : wsize) (f : nat -> bool) : word ws :=
  let bits := map f (iota 0 (wsize_size_minus_1 ws).+1) in
  t2w (Tuple (tval := bits) ltac:(by rewrite size_map size_iota)).

Definition add_word {s} (x y: word s) : word s := add_word x y.
Definition sub_word {s} (x y: word s) : word s := sub_word x y.
Definition mul_word {s} (x y: word s) : word s := mul_word x y.
Definition opp_word {s} (x: word s) : word s := opp_word x.

Declare Scope word_scope.
Delimit Scope word_scope with w.

Definition word0 {s} : word s := word0.
Definition word1 {s} : word s := word1 _.

Notation "0" := word0 : word_scope.
Notation "1" := word1 : word_scope.
Notation "+%w" := add_word : function_scope.
Notation "*%w" := mul_word : function_scope.
Notation "-%w" := opp_word : function_scope.

Notation "w1 + w2" := (add_word w1%w w2%w) : word_scope.
Notation "w1 * w2" := (mul_word w1%w w2%w) : word_scope.
Notation "w1 - w2" := (sub_word w1%w w2%w) : word_scope.
Notation "- w" := (opp_word w%w) : word_scope.

Lemma add_wordE {ws} (w1 w2 : word ws) : (w1 + w2)%w = (w1 + w2)%R.
Proof. reflexivity. Qed.

Lemma sub_wordE {ws} (w1 w2 : word ws) : (w1 - w2)%w = (w1 - w2)%R.
Proof. exact: sub_wordE. Qed.

Definition wand {s} (x y: word s) : word s := wand x y.
Definition wor {s} (x y: word s) : word s := wor x y.
Definition wxor {s} (x y: word s) : word s := wxor x y.

Definition wlt {sz} (sg: signedness) : word sz → word sz → bool :=
  match sg with
  | Unsigned => λ x y, (urepr x <? urepr y)%Z
  | Signed => λ x y, (srepr x <? srepr y)%Z
  end.

Definition wle sz (sg: signedness) : word sz → word sz → bool :=
  match sg with
  | Unsigned => λ x y, (urepr x <=? urepr y)%Z
  | Signed => λ x y, (srepr x <=? srepr y)%Z
  end.

Definition wnot sz (w: word sz) : word sz :=
  wxor w (-1%w)%w.

Arguments wnot {sz} w.

Definition wandn sz (x y: word sz) : word sz := wand (wnot x) y.

Definition wunsigned {s} (w: word s) : Z :=
  urepr w.
Arguments wunsigned : simpl never.

Definition wsigned {s} (w: word s) : Z :=
  srepr w.
Arguments wsigned : simpl never.

Definition wrepr s (z: Z) : word s :=
  mkword (wsize_size_minus_1 s).+1 z.

Lemma wunsigned_inj sz : injective (@wunsigned sz).
Proof. by move => x y /eqP /val_eqP. Qed.

Lemma wrepr_unsigned s (w: word s) : wrepr s (wunsigned w) = w.
Proof. by rewrite /wrepr /wunsigned ureprK. Qed.

Lemma wunsigned_repr s z :
  wunsigned (wrepr s z) = z mod modulus (wsize_size_minus_1 s).+1.
Proof. by rewrite /wunsigned /wrepr mkwordK. Qed.

Lemma wrepr0 sz : wrepr sz 0 = 0%R.
Proof. by apply/eqP. Qed.

Lemma wreprB sz : wrepr sz (wbase sz) = 0%R.
Proof. by apply/eqP;case sz. Qed.

Lemma wunsigned_range sz (p: word sz) :
  0 <= wunsigned p < wbase sz.
Proof. by have /iswordZP := isword_word p. Qed.

Lemma wunsigned_repr_small ws z : 0 <= z < wbase ws -> wunsigned (wrepr ws z) = z.
Proof. move=> h; rewrite wunsigned_repr; apply: Zmod_small h. Qed.

Lemma wrepr_add sz (x y: Z) :
  wrepr sz (x + y) = (wrepr sz x + wrepr sz y)%R.
Proof.
  apply: wunsigned_inj.
  by rewrite wunsigned_repr Zplus_mod /wunsigned addwE !mkwordK.
Qed.

Lemma wrepr_sub sz (x y: Z) :
  wrepr sz (x - y) = (wrepr sz x - wrepr sz y)%R.
Proof.
  apply: wunsigned_inj.
  by rewrite wunsigned_repr Zminus_mod /wunsigned subwE !mkwordK.
Qed.

Lemma wrepr_mul sz (x y: Z) :
  wrepr sz (x * y) = (wrepr sz x * wrepr sz y)%R.
Proof.
  apply: wunsigned_inj.
  by rewrite wunsigned_repr Zmult_mod /wunsigned mulwE !mkwordK.
Qed.

Lemma wrepr_m1 sz :
  wrepr sz (-1) = (-1)%R.
Proof. by apply /eqP; case sz. Qed.

Lemma wrepr_opp sz (x: Z) :
  wrepr sz (- x) = (- wrepr sz x)%R.
Proof.
  have -> : (- x) = (- x)%R by done.
  by rewrite -(mulN1r x) wrepr_mul wrepr_m1 mulN1r.
Qed.

Lemma wunsigned_add sz (p: word sz) (n: Z) :
  0 <= wunsigned p + n < wbase sz →
  wunsigned (p + wrepr sz n) = wunsigned p + n.
Proof.
  move=> h.
  rewrite -{1}(wrepr_unsigned p).
  by rewrite -wrepr_add wunsigned_repr Z.mod_small.
Qed.

Lemma wunsigned_sub (sz : wsize) (p : word sz) (n : Z):
  0 <= wunsigned p - n < wbase sz → wunsigned (p - wrepr sz n) = wunsigned p - n.
Proof.
  move=> h.
  rewrite -{1}(wrepr_unsigned p).
  by rewrite -wrepr_sub wunsigned_repr Z.mod_small.
Qed.

Lemma wunsigned_sub_if ws (a b : word ws) :
  wunsigned (a - b) =
    if wunsigned b <=? wunsigned a then wunsigned a - wunsigned b
    else  wbase ws + wunsigned a - wunsigned b.
Proof.
  move: (wunsigned_range a) (wunsigned_range b).
  rewrite /wunsigned mathcomp.word.word.subwE -/(wbase ws) => ha hb.
  have -> : (word.urepr a - word.urepr b)%R = word.urepr a - word.urepr b by done.
  case: ZleP => hle.
  + by rewrite Zmod_small //; lia.
  by rewrite -(Z_mod_plus_full _ 1) Zmod_small; lia.
Qed.

Lemma wunsigned_sub_mod ws ws' (w1 w2 : word ws) :
  wunsigned (w1 - w2) mod wsize_size ws' = (wunsigned w1 - wunsigned w2) mod wsize_size ws'.
Proof.
  rewrite wunsigned_sub_if.
  case: ZleP => // _.
  rewrite -Z.add_sub_assoc Zplus_mod.
  rewrite (Znumtheory.Zdivide_mod _ _ (wsize_size_div_wbase _ _)) Z.add_0_l.
  by rewrite Zmod_mod.
Qed.

Definition wshr sz (x: word sz) (n: Z) : word sz :=
  mkword sz (Z.shiftr (wunsigned x) (Z.min (wsize_bits sz) n)).

Definition wshr_naive sz (x: word sz) (n: Z) : word sz :=
  mkword sz (Z.shiftr (wunsigned x) n).

Lemma wshr_alt sz (x: word sz) n :
  wshr x n = wshr_naive x n.
Proof.
  rewrite /wshr /wshr_naive.
  case: (Z.min_spec (wsize_bits sz) n) => - [] h ->; last reflexivity.
  have hr := wunsigned_range x.
  have ? := log2_wsize_bits hr.
  case: hr => ??.
  rewrite !Z.shiftr_eq_0 //; lia.
Qed.

Definition wshl sz (x: word sz) (n: Z) : word sz :=
  mkword sz (Z.shiftl (wunsigned x) (Z.min (wsize_bits sz) n)).

Definition wshl_naive sz (x: word sz) (n: Z) : word sz :=
  mkword sz (Z.shiftl (wunsigned x) n).

Lemma wshl_alt sz (x: word sz) n :
  wshl x n = wshl_naive x n.
Proof.
  rewrite /wshl.
  case: (Z.min_spec (wsize_bits sz) n) => - [] h ->; last reflexivity.
  have h0 : 0 <= wsize_bits sz by case: (sz).
  rewrite /wshl_naive -!/(wrepr sz _).
  have -> : n = wsize_bits sz + (n - wsize_bits sz) by lia.
  rewrite -Z.shiftl_shiftl //.
  rewrite !Z.shiftl_mul_pow2; only 2, 3: lia.
  by rewrite !wrepr_mul wsize_bits_wbase wreprB mulr0 mul0r.
Qed.

Definition wsar sz (x: word sz) (n: Z) : word sz :=
  mkword sz (Z.shiftr (wsigned x) (Z.min (wsize_bits sz) n)).

Definition wsar_naive sz (x: word sz) (n: Z) : word sz :=
  mkword sz (Z.shiftr (wsigned x) n).

Definition high_bits sz (n : Z) : word sz :=
  wrepr sz (Z.shiftr n (wsize_bits sz)).

Definition wmulhu sz (x y: word sz) : word sz :=
  high_bits sz (wunsigned x * wunsigned y).

Definition wmulhs sz (x y: word sz) : word sz :=
  high_bits sz (wsigned x * wsigned y).

Definition wmulhsu sz (x y: word sz) : word sz :=
  high_bits sz (wsigned x * wunsigned y).

Definition wmulhrs sz (x y: word sz) : word sz :=
  let: p := (Z.shiftr (wsigned x * wsigned y) (Z.of_nat (wsize_size_minus_1 sz).-1) + 1)%Z in
  wrepr sz (Z.shiftr p 1).

Definition wmax_unsigned sz := wbase sz - 1.

Definition half_modulus sz : Z := modulus (wsize_size_minus_1 sz).
Definition wmin_signed (sz: wsize) : Z := -half_modulus sz.
Definition wmax_signed (sz: wsize) : Z := half_modulus sz - 1.

Notation u8   := (word U8).
Notation u16  := (word U16).
Notation u32  := (word U32).
Notation u64  := (word U64).
Notation u128 := (word U128).
Notation u256 := (word U256).

Definition wbit_n sz (w:word sz) (n:nat) : bool :=
   wbit (wunsigned w) n.

Lemma eq_from_wbit_n s (w1 w2: word s) :
  reflect (∀ i : 'I_(wsize_size_minus_1 s).+1, wbit_n w1 i = wbit_n w2 i) (w1 == w2).
Proof. apply/eq_from_wbit. Qed.

Lemma wandE s (w1 w2: word s) i :
  wbit_n (wand w1 w2) i = wbit_n w1 i && wbit_n w2 i.
Proof. by rewrite /wbit_n /wand wandE. Qed.

Lemma w0E sz i :
  @wbit_n sz 0%R i  = false.
Proof. exact: wbit0. Qed.

Lemma wshrE sz (x: word sz) c i :
  0 <= c →
  wbit_n (wshr x c) i = wbit_n x (Z.to_nat c + i).
Proof.
  move/Z2Nat.id => {1}<-.
  rewrite wshr_alt /wshr_naive -urepr_lsr ureprK.
  exact: wbit_lsr.
Qed.

Lemma wunsigned_wshr sz (x: word sz) c :
  wunsigned (wshr x (Z.of_nat c)) = wunsigned x / 2 ^ Z.of_nat c.
Proof.
  have rhs_range : 0 <= wunsigned x / 2 ^ Z.of_nat c ∧ wunsigned x / 2 ^ Z.of_nat c < modulus sz.
  - have x_range := wunsigned_range x.
    split.
    + apply: Z.div_pos; first lia.
      apply: Z.pow_pos_nonneg; lia.
     change (modulus sz) with (wbase sz).
     elim_div => ? ? []; last nia.
     apply: Z.pow_nonzero; lia.
  rewrite -(Z.mod_small (wunsigned x / 2 ^ Z.of_nat c) (modulus sz)) //.
  rewrite -wunsigned_repr.
  congr wunsigned.
  rewrite wshr_alt /wshr_naive -urepr_lsr ureprK.
  apply/eqP/eq_from_wbit_n => i.
  rewrite /wbit_n wbit_lsr wunsigned_repr !wbit_spec.
  rewrite Z.mod_small //.
  rewrite Z.div_pow2_bits.
  2-3: lia.
  by rewrite Nat2Z.n2zD Z.add_comm.
Qed.

Lemma wshlE sz (w: word sz) c i :
  0 <= c →
  wbit_n (wshl w c) i = (Z.to_nat c <= i <= wsize_size_minus_1 sz)%nat && wbit_n w (i - Z.to_nat c).
Proof.
  move/Z2Nat.id => {1}<-.
  rewrite /wbit_n wshl_alt /wshl_naive /=.
  case: leP => hic /=;
    last (rewrite wbit_lsl_lo //; apply/leP; lia).
  have eqi : (Z.to_nat c + (i - Z.to_nat c))%nat = i.
   * by rewrite /addn; zify; rewrite Nat2Z.inj_sub; lia.
  have := wbit_lsl w (Z.to_nat c) (i - Z.to_nat c).
  by rewrite eqi => ->.
Qed.

Local Ltac lia :=
  rewrite /addn /subn; Lia.lia.

Lemma wunsigned_wshl sz (x: word sz) c :
  wunsigned (wshl x (Z.of_nat c)) = (wunsigned x * 2 ^ Z.of_nat c) mod wbase sz.
Proof.
  rewrite -wunsigned_repr wshl_alt.
  congr wunsigned.
  apply/eqP/eq_from_wbit_n => i.
  rewrite /wbit_n wunsigned_repr /modulus two_power_nat_equiv.
  rewrite (wbit_spec (_ mod _)) Z.mod_pow2_bits_low; last first.
  - move/ltP: (ltn_ord i); lia.
  case: (@ltP i c); last first.
  - move => c_le_i.
    have i_eq : nat_of_ord i = (c + (i - c))%nat by lia.
    rewrite i_eq wbit_lsl -i_eq ltn_ord wbit_spec.
    rewrite Z.mul_pow2_bits; last by lia.
    congr Z.testbit.
    lia.
  move => l_lt_c.
  rewrite wbit_lsl_lo; last by apply/ltP.
  rewrite Z.mul_pow2_bits_low //; lia.
Qed.

Definition lsb {s} (w: word s) : bool := wbit_n w 0.
Definition msb {s} (w: word s) : bool := wbit_n w (wsize_size_minus_1 s).

Definition wdwordu sz (hi lo: word sz) : Z :=
  wbase sz * wunsigned hi + wunsigned lo.

Definition wdwords sz (hi lo: word sz) : Z :=
  wbase sz * wsigned hi + wunsigned lo.

Definition waddcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x + wunsigned y + Z.b2z c in
  (wbase sz <=? n, wrepr sz n).

Definition wdaddu sz (hi_1 lo_1 hi_2 lo_2: word sz) :=
  let n := (wdwordu hi_1 lo_1) + (wdwordu hi_2 lo_2) in
  (wrepr sz n, high_bits sz n).

Definition wdadds sz (hi_1 lo_1 hi_2 lo_2: word sz) :=
  let n := (wdwords hi_1 lo_1) + (wdwords hi_2 lo_2) in
  (wrepr sz n, high_bits sz n).

Definition wsubcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x - wunsigned y - Z.b2z c in
  (n <? 0, wrepr sz n).

Definition wumul sz (x y: word sz) :=
  let n := wunsigned x * wunsigned y in
  (high_bits sz n, wrepr sz n).

Definition wsmul sz (x y: word sz) :=
  let n := wsigned x * wsigned y in
  (high_bits sz n, wrepr sz n).

Definition wdiv {sz} (p q : word sz) : word sz :=
  let p := wunsigned p in
  let q := wunsigned q in
  wrepr sz (p / q)%Z.

Definition wdivi {sz} (p q : word sz) : word sz :=
  let p := wsigned p in
  let q := wsigned q in
  wrepr sz (Z.quot p q)%Z.

Definition wmod {sz} (p q : word sz) : word sz :=
  let p := wunsigned p in
  let q := wunsigned q in
  wrepr sz (p mod q)%Z.

Definition wmodi {sz} (p q : word sz) : word sz :=
  let p := wsigned p in
  let q := wsigned q in
  wrepr sz (Z.rem p q)%Z.

Definition zero_extend sz sz' (w: word sz') : word sz :=
  wrepr sz (wunsigned w).

Definition sign_extend sz sz' (w: word sz') : word sz :=
  wrepr sz (wsigned w).

Definition truncate_word s s' (w:word s') : exec (word s) :=
  match gcmp s s' as c return gcmp s s' = c → exec (word s) with
  | Eq => λ h, ok (ecast s (word s) (esym (cmp_eq h)) w)
  | Lt => λ _, ok (zero_extend s w)
  | Gt => λ _, type_error
  end erefl.

Variant truncate_word_spec s s' (w: word s') : exec (word s) → Type :=
  | TruncateWordEq (h: s' = s) : truncate_word_spec (ok (ecast s (word s) h w))
  | TruncateWordLt (h: (s < s')%CMP) : truncate_word_spec (ok (zero_extend s w))
  | TruncateWordGt : (s' < s)%CMP → truncate_word_spec type_error
  .

Lemma truncate_wordP' s s' (w: word s') : truncate_word_spec w (truncate_word s w).
Proof.
  rewrite /truncate_word/gcmp.
  case: {2 3} (wsize_cmp s s') erefl.
  - move => /cmp_eq ?; exact: TruncateWordEq.
  - move => h; apply: TruncateWordLt.
    by rewrite /cmp_lt /gcmp h.
  rewrite -/(gcmp s s') => h.
  apply: TruncateWordGt.
  by rewrite /cmp_lt cmp_sym h.
Qed.

Definition wbit sz (w i: word sz) : bool :=
  wbit_n w (Z.to_nat (wunsigned i mod wsize_bits sz)).

Definition wror sz (w:word sz) (z:Z) :=
  let i := zmod_pow2 z (wsize_log2 sz).+3 in
  wor (wshr_naive w i) (wshl_naive w (wsize_bits sz - i)).

Definition wrol sz (w: word sz) (z: Z) :=
  let i := zmod_pow2 z (wsize_log2 sz).+3 in
  wor (wshl_naive w i) (wshr_naive w (wsize_bits sz - i)).

(* -------------------------------------------------------------------*)

(* -------------------------------------------------------------------*)

(* -------------------------------------------------------------------*)

(* -------------------------------------------------------------------*)

Lemma zero_extend_u sz (w:word sz) : zero_extend sz w = w.
Proof. by rewrite /zero_extend wrepr_unsigned. Qed.

Lemma zero_extend_wrepr sz sz' z :
  (sz <= sz')%CMP →
  zero_extend sz (wrepr sz' z) = wrepr sz z.
Proof.
move/wsize_size_m => hle.
apply: wunsigned_inj.
rewrite !wunsigned_repr.
case: (modulus_m hle) => n -> {hle}.
exact: mod_pq_mod_q.
Qed.

Lemma zero_extend_idem s s1 s2 (w:word s) :
  (s1 <= s2)%CMP -> zero_extend s1 (zero_extend s2 w) = zero_extend s1 w.
Proof.
  by move=> hle;rewrite [X in (zero_extend _ X) = _]/zero_extend zero_extend_wrepr.
Qed.

Lemma truncate_word_le s s' (w: word s') :
  (s ≤ s')%CMP →
  truncate_word s w = ok (zero_extend s w).
Proof.
  case: truncate_wordP' => //.
  - by move => ?; subst; rewrite zero_extend_u.
  by rewrite -cmp_nle_lt => /negbTE ->.
Qed.

Lemma truncate_wordP s1 s2 (w1:word s1) (w2:word s2) :
  truncate_word s1 w2 = ok w1 → (s1 <= s2)%CMP /\ w1 = zero_extend s1 w2.
Proof.
  case: truncate_wordP'; last by [].
  - move => ?; subst => /ok_inj ->{w2}.
    by rewrite cmp_le_refl zero_extend_u.
  by move => /(@cmp_lt_le _ _ _ _ _) -> /ok_inj ->.
Qed.

Global Opaque truncate_word.

Lemma truncate_word_u s (a : word s) : truncate_word s a = ok a.
Proof. by rewrite truncate_word_le ?zero_extend_u ?cmp_refl. Qed.


(* -------------------------------------------------------------------*)

(* -------------------------------------------------------------------*)

(* -------------------------------------------------------------------*)

(* -------------------------------------------------------------------*)
Definition check_scale (s:Z) :=
  (s == 1%Z) || (s == 2%Z) || (s == 4%Z) || (s == 8%Z).

(* -------------------------------------------------------------------*)
Definition mask_word (sz:wsize) : u64 :=
  match sz with
  | U8 | U16 => wshl (-1)%R (wsize_bits sz)
  | _ => 0%R
  end.

(* -------------------------------------------------------------------*)
Definition split_vec {sz} ve (w : word sz) :=
  let wsz := (sz %/ ve + sz %% ve)%nat in
  [seq subword (i * ve)%nat ve w | i <- iota 0 wsz].

Definition make_vec {sz} sz' (s : seq (word sz)) :=
  wrepr sz' (wcat_r s).

Lemma make_vec_split_vec sz w :
  make_vec sz (split_vec U8 w) = w.
Proof.
have mod0: sz %% U8 = 0%nat by case: {+}sz.
have sz_even: sz = (U8 * (sz %/ U8))%nat :> nat.
+ by rewrite [LHS](divn_eq _ U8) mod0 addn0 mulnC.
rewrite /make_vec /split_vec mod0 addn0; set s := map _ _.
pose wt := (ecast ws (ws.-word) sz_even w).
pose t  := [tuple subword (i * U8) U8 wt | i < sz %/ U8].
have eq_st: wcat_r s = wcat t.
+ rewrite {}/s {}/t /=; pose F i := subword (i * U8) U8 wt.
  rewrite (map_comp F val) val_enum_ord {}/F.
  congr wcat_r; apply/eq_map => i; apply/eqP/eq_from_wbit.
  move=> j; rewrite !subwordE; congr (mathcomp.word.word.wbit (t2w _) _).
  apply/val_eqP/eqP => /=; apply/eq_map=> k.
  suff ->: val wt = val w by done.
  by rewrite {}/wt; case: _ / sz_even.
rewrite {}eq_st wcat_subwordK {s t}/wt; case: _ / sz_even.
by rewrite /wrepr /= ureprK.
Qed.

Lemma mkwordI n x y :
  (0 <= x < modulus n)%R ->
  (0 <= y < modulus n)%R ->
  mkword n x = mkword n y -> x = y.
Proof.
case/andP => /ZleP ? /ZltP ? /andP[] /ZleP ? /ZltP ? h.
have : urepr (mkword n x) = urepr (mkword n y) by rewrite h.
by clear h; rewrite !mkwordK !Z.mod_small.
Qed.

Lemma make_vec_inj sz (bs bs': seq u8) :
  size bs = size bs' →
  size bs = Z.to_nat (wsize_size sz) →
  make_vec sz bs = make_vec sz bs' →
  bs = bs'.
Proof.
Transparent word.
rewrite /make_vec /wrepr /word.
Opaque word.
have : (wsize_size_minus_1 sz).+1 = (8 * Z.to_nat (wsize_size sz))%nat by case: sz.
move: (wsize_size sz) => n /= ->.
move: {n} (Z.to_nat n) => n.
move => eq_size <- /mkwordI.
rewrite {2}eq_size => /(_ (wcat_subproof (in_tuple bs)) (wcat_subproof (in_tuple bs'))).
exact: wcat_rI eq_size.
Qed.

(* -------------------------------------------------------------------*)
Definition lift1_vec' ve ve' (op : word ve → word ve')
    (sz sz': wsize) (w: word sz) : word sz' :=
  make_vec sz' (map op (split_vec ve w)).

Definition lift1_vec ve (op : word ve -> word ve)
    (sz:wsize) (w:word sz) : word sz :=
  lift1_vec' op sz w.
Arguments lift1_vec : clear implicits.

Definition lift2_vec ve (op : word ve -> word ve -> word ve)
  (sz:wsize) (w1 w2:word sz) : word sz :=
  make_vec sz (map2 op (split_vec ve w1) (split_vec ve w2)).
Arguments lift2_vec : clear implicits.

(* -------------------------------------------------------------------*)
Definition wbswap sz (w: word sz) : word sz :=
  make_vec sz (rev (split_vec U8 w)).

(* -------------------------------------------------------------------*)
(* Bit [i] of the operand is bit [wsize_bits sz - 1 - i] of the result. *)
Definition wbitrev sz (w: word sz) : word sz :=
  winit sz (fun i => wbit_n w (wsize_size_minus_1 sz - i)).

(* -------------------------------------------------------------------*)
Definition popcnt sz (w: word sz) :=
 wrepr sz (Z.of_nat (count id (w2t w))).

(* -------------------------------------------------------------------*)
Definition pextr sz (w1 w2: word sz) :=
 wrepr sz (t2w (in_tuple (mask (w2t w2) (w2t w1)))).

(* -------------------------------------------------------------------*)

Fixpoint bitpdep sz (w:word sz) (i:nat) (mask:bitseq) :=
  match mask with
  | [::] => [::]
  | b :: mask =>
      if b then wbit_n w i :: bitpdep w (i.+1) mask
      else false :: bitpdep w i mask
  end.

Definition pdep sz (w1 w2: word sz) :=
 wrepr sz (t2w (in_tuple (bitpdep w1 0 (w2t w2)))).

(* -------------------------------------------------------------------*)

Fixpoint leading_zero_aux (n : Z) (res sz : nat) : nat :=
  if (n <? 2 ^ Z.of_nat (sz - res))%Z
  then res
  else
    match res with
    | O => O
    | S res' => leading_zero_aux n res' sz
    end.

Definition leading_zero (sz : wsize) (w : word sz) : word sz :=
  wrepr sz (Z.of_nat (leading_zero_aux (wunsigned w) sz sz)).

Definition trailing_zero_aux (n: Z) (bits: nat) : nat :=
  if n is Zpos p then
    (fix tzcnt acc p := if p is xO q then tzcnt acc.+1 q else acc) O p
  else bits.

Definition trailing_zero (sz : wsize) (w : word sz) : word sz :=
  wrepr sz (Z.of_nat (trailing_zero_aux (wunsigned w) sz)).

(* -------------------------------------------------------------------*)
Definition halve_list A : seq A → seq A :=
  fix loop m := if m is a :: _ :: m' then a :: loop m' else m.

Definition wpmul sz (x y: word sz) : word sz :=
  let xs := halve_list (split_vec U32 x) in
  let ys := halve_list (split_vec U32 y) in
  let f (a b: u32) : u64 := wrepr U64 (wsigned a * wsigned b) in
  make_vec sz (map2 f xs ys).

Definition wpmulu sz (x y: word sz) : word sz :=
  let xs := halve_list (split_vec U32 x) in
  let ys := halve_list (split_vec U32 y) in
  let f (a b: u32) : u64 := wrepr U64 (wunsigned a * wunsigned b) in
  make_vec sz (map2 f xs ys).

(* -------------------------------------------------------------------*)
Definition wpshufb1 (s : seq u8) (idx : u8) : u8 :=
  if msb idx then 0%w else
    let off := wunsigned (wand idx (wshl 1%w 4%Z - 1%w)%w) in
    nth 0%w s (Z.to_nat off).

Definition wpshufb (sz: wsize) (w idx: word sz) : word sz :=
  let s := split_vec 8 w in
  let i := split_vec 8 idx in
  let r := map (wpshufb1 s) i in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Definition wpshufd1 (s : u128) (o : u8) (i : nat) :=
  subword 0 32 (wshr s (32 * urepr (subword (2 * i) 2 o))).

Definition wpshufd_128 (s : u128) (o : Z) : u128 :=
  let o := wrepr U8 o in
  let d := [seq wpshufd1 s o i | i <- iota 0 4] in
  wrepr U128 (wcat_r d).

Definition wpshufd_256 (s : u256) (o : Z) : u256 :=
  make_vec U256 (map (λ w, wpshufd_128 w o) (split_vec U128 s)).

Definition wpshufd sz : word sz → Z → word sz :=
  match sz with
  | U128 => wpshufd_128
  | U256 => wpshufd_256
  | _ => λ w _, w end.

(* -------------------------------------------------------------------*)

Definition wpshufl_u64 (w:u64) (z:Z) : u64 :=
  let v := split_vec U16 w in
  let j := split_vec 2 (wrepr U8 z) in
  make_vec U64 (map (λ n, nth 0%w v (Z.to_nat (urepr n))) j).

Definition wpshufl_u128 (w:u128) (z:Z) :=
  match split_vec 64 w with
  | [::l;h] => make_vec U128 [::wpshufl_u64 l z; (h:u64)]
  | _       => w
  end.

Definition wpshufh_u128 (w:u128) (z:Z) :=
  match split_vec 64 w with
  | [::l;h] => make_vec U128 [::(l:u64); wpshufl_u64 h z]
  | _       => w
  end.

Definition wpshufl_u256 (s:u256) (z:Z) :=
  make_vec U256 (map (λ w, wpshufl_u128 w z) (split_vec U128 s)).

Definition wpshufh_u256 (s:u256) (z:Z) :=
  make_vec U256 (map (λ w, wpshufh_u128 w z) (split_vec U128 s)).

Definition wpshuflw sz : word sz → Z → word sz :=
  match sz with
  | U128 => wpshufl_u128
  | U256 => wpshufl_u256
  | _ => λ w _, w end.

Definition wpshufhw sz : word sz → Z → word sz :=
  match sz with
  | U128 => wpshufh_u128
  | U256 => wpshufh_u256
  | _ => λ w _, w end.

(* -------------------------------------------------------------------*)

(*Section UNPCK.
  (* Interleaves two even-sized lists. *)
  Context (T: Type).
  Fixpoint unpck (qs xs ys: seq T) : seq T :=
    match xs, ys with
    | [::], _ | _, [::]
    | [:: _], _ | _, [:: _]
      => qs
    | x :: _ :: xs', y :: _ :: ys' => unpck (x :: y :: qs) xs' ys'
    end.
End UNPCK.

Definition wpunpckl sz (ve: velem) (x y: word sz) : word sz :=
  let xv := split_vec ve x in
  let yv := split_vec ve y in
  let zv := unpck [::] xv yv in
  make_vec sz (rev zv).

Definition wpunpckh sz (ve: velem) (x y: word sz) : word sz :=
  let xv := split_vec ve x in
  let yv := split_vec ve y in
  let zv := unpck [::] (rev xv) (rev yv) in
  make_vec sz zv.
*)

Fixpoint interleave {A:Type} (l1 l2: list A) :=
  match l1, l2 with
  | [::], _ => l2
  | _, [::] => l1
  | a1::l1, a2::l2 => a1::a2::interleave l1 l2
  end.

Definition interleave_gen (get:u128 -> u64) (ve:velem) (src1 src2: u128) :=
  let ve : nat :=  wsize_of_velem ve in
  let l1 := split_vec ve (get src1) in
  let l2 := split_vec ve (get src2) in
  make_vec U128 (interleave l1 l2).

Definition wpunpckl_128 := interleave_gen (subword 0 64).

Definition wpunpckl_256 ve (src1 src2 : u256) :=
  make_vec U256
    (map2 (wpunpckl_128 ve) (split_vec U128 src1) (split_vec U128 src2)).

Definition wpunpckh_128 := interleave_gen (subword 64 64).

Definition wpunpckh_256 ve (src1 src2 : u256) :=
  make_vec U256
    (map2 (wpunpckh_128 ve) (split_vec U128 src1) (split_vec U128 src2)).

Definition wpunpckl (sz:wsize) : velem -> word sz -> word sz -> word sz :=
  match sz with
  | U128 => wpunpckl_128
  | U256 => wpunpckl_256
  | _    => fun ve w1 w2 => w1
  end.

Definition wpunpckh (sz:wsize) : velem -> word sz -> word sz -> word sz :=
  match sz with
  | U128 => wpunpckh_128
  | U256 => wpunpckh_256
  | _    => fun ve w1 w2 => w1
  end.

(* -------------------------------------------------------------------*)
Section UPDATE_AT.
  Context (T: Type) (t: T).

  Fixpoint update_at (xs: seq T) (i: nat) : seq T :=
    match xs with
    | [::] => [::]
    | x :: xs' => if i is S i' then x :: update_at xs' i' else t :: xs'
    end.

End UPDATE_AT.

Definition wpinsr ve (v: u128) (w: word ve) (i: u8) : u128 :=
  let v := split_vec ve v in
  let i := Z.to_nat (wunsigned i) in
  make_vec U128 (update_at w v i).

(* -------------------------------------------------------------------*)
Definition winserti128 (v: u256) (w: u128) (i: u8) : u256 :=
  let v := split_vec U128 v in
  make_vec U256 (if lsb i then [:: nth 0%w v 0 ; w ] else [:: w ; nth 0%w v 1 ]).

(* -------------------------------------------------------------------*)
Definition wpblendd sz (w1 w2: word sz) (m: u8) : word sz :=
  let v1 := split_vec U32 w1 in
  let v2 := split_vec U32 w2 in
  let b := split_vec 1 m in
  let r := map3 (λ b v1 v2, if b == word.word.word1 _ then v2 else v1) b v1 v2 in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Definition wpbroadcast ve sz (w: word ve) : word sz :=
  let r := nseq (sz %/ ve) w in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Fixpoint seq_dup_hi T (m: seq T) : seq T :=
  if m is _ :: a :: m' then a :: a :: seq_dup_hi m' else [::].

Fixpoint seq_dup_lo T (m: seq T) : seq T :=
  if m is a :: _ :: m' then a :: a :: seq_dup_lo m' else [::].

Definition wdup_hi ve sz (w: word sz) : word sz :=
  let v : seq (word ve) := split_vec ve w in
  make_vec sz (seq_dup_hi v).

Definition wdup_lo ve sz (w: word sz) : word sz :=
  let v : seq (word ve) := split_vec ve w in
  make_vec sz (seq_dup_lo v).

(* -------------------------------------------------------------------*)
Definition wperm2i128 (w1 w2: u256) (i: u8) : u256 :=
  let choose (n: nat) :=
      match urepr (subword n 2 i) with
      | 0 => subword 0 U128 w1
      | 1 => subword U128 U128 w1
      | 2 => subword 0 U128 w2
      | _ => subword U128 U128 w2
      end in
  let lo := if wbit_n i 3 then 0%w else choose 0%nat in
  let hi := if wbit_n i 7 then 0%w else choose 4%nat in
  make_vec U256 [:: lo ; hi ].

(* -------------------------------------------------------------------*)
Definition wpermd1 (v: seq u32) (idx: u32) :=
  let off := wunsigned idx mod 8 in
  (nth 0%w v (Z.to_nat off)).

Definition wpermd sz (idx w: word sz) : word sz :=
  let v := split_vec U32 w in
  let i := split_vec U32 idx in
  make_vec sz (map (wpermd1 v) i).

(* -------------------------------------------------------------------*)
Definition wpermq (w: u256) (i: u8) : u256 :=
  let v := split_vec U64 w in
  let j := split_vec 2 i in
  make_vec U256 (map (λ n, nth 0%w v (Z.to_nat (urepr n))) j).

(* -------------------------------------------------------------------*)
Definition wpsxldq op sz (w: word sz) (i: u8) : word sz :=
  let n : Z := (Z.min 16 (wunsigned i)) * 8 in
  lift1_vec U128 (λ w, op w n) sz w.

Definition wpslldq := wpsxldq (@wshl _).
Definition wpsrldq := wpsxldq (@wshr _).

(* -------------------------------------------------------------------*)
Definition wpcmps1 (cmp: Z → Z → bool) ve (x y: word ve) : word ve :=
  if cmp (wsigned x) (wsigned y) then (- 1%w)%w else 0%w.
Arguments wpcmps1 cmp {ve} _ _.

Definition wpcmpeq ve sz (w1 w2: word sz) : word sz :=
  lift2_vec ve (wpcmps1 Z.eqb) sz w1 w2.

Definition wpcmpgt ve sz (w1 w2: word sz) : word sz :=
  lift2_vec ve (wpcmps1 Z.gtb) sz w1 w2.

(* -------------------------------------------------------------------*)
Definition wminmax1 ve (cmp : word ve -> word ve -> bool) (x y : word ve) : word ve :=
  if cmp x y then x else y.

Definition wmin sg ve sz (x y : word sz) :=
  lift2_vec ve (wminmax1 (wlt sg)) sz x y.

Definition wmax sg ve sz (x y : word sz) :=
  lift2_vec ve (wminmax1 (fun u v => wlt sg v u)) sz x y.

(* -------------------------------------------------------------------*)

Definition wabs (ve: velem) :=
  lift1_vec ve (λ x, wrepr ve (Z.abs (wsigned x))).

(* -------------------------------------------------------------------*)
Definition saturated_signed (sz: wsize) (x: Z): Z :=
 Z.max (wmin_signed sz) (Z.min (wmax_signed sz) x).

Definition wrepr_saturated_signed (sz: wsize) (x: Z) : word sz :=
 wrepr sz (saturated_signed sz x).

Fixpoint add_pairs (m: seq Z) : seq Z :=
  if m is x :: y :: z then x + y :: add_pairs z
  else [::].

Definition wpmaddubsw sz (v1 v2: word sz) : word sz :=
  let w1 := map wunsigned (split_vec U8 v1) in
  let w2 := map wsigned (split_vec U8 v2) in
  let result := [seq wrepr_saturated_signed U16 z | z <- add_pairs (map2 Z.mul w1 w2) ] in
  make_vec sz result.

Definition wpmaddwd sz (v1 v2: word sz) : word sz :=
  let w1 := map wsigned (split_vec U16 v1) in
  let w2 := map wsigned (split_vec U16 v2) in
  let result := [seq wrepr U32 z | z <- add_pairs (map2 Z.mul w1 w2) ] in
  make_vec sz result.

(* -------------------------------------------------------------------*)
Definition wpack sz pe (arg: seq Z) : word sz :=
  let w := map (mathcomp.word.word.mkword pe) arg in
  wrepr sz (word.wcat_r w).

(* -------------------------------------------------------------------*)
Definition movemask (ve: velem) (ssz: wsize) (w : word ssz) : word U32 :=
  wrepr U32 (t2w_def [tuple of map msb (split_vec ve w)]).

(* -------------------------------------------------------------------*)
Definition blendv (ve: velem) sz (w1 w2 m: word sz): word sz :=
  let v1 := split_vec ve w1 in
  let v2 := split_vec ve w2 in
  let b  := map msb (split_vec ve m)  in
  let r := map3 (fun bi v1i v2i => if bi then v2i else v1i) b v1 v2 in
  make_vec sz r.

Definition wpblendvb := blendv VE8.

(* -------------------------------------------------------------------*)
Lemma pow2pos q : 0 < 2 ^ Z.of_nat q.
Proof. by rewrite -two_power_nat_equiv. Qed.

Lemma pow2nz q : 2 ^ Z.of_nat q ≠ 0.
Proof. have := pow2pos q; lia. Qed.

Lemma wbit_n_pow2m1 sz (n i: nat) :
  wbit_n (wrepr sz (2 ^ Z.of_nat n - 1)) i = (i < Nat.min n (wsize_size_minus_1 sz).+1)%nat.
Proof.
  rewrite /wbit_n wbit_spec wunsigned_repr /modulus two_power_nat_equiv.
  case: (le_lt_dec (wsize_size_minus_1 sz).+1 i) => hi.
  - rewrite Z.mod_pow2_bits_high; last lia.
    symmetry; apply/negbTE/negP => /ltP.
    lia.
  rewrite Z.mod_pow2_bits_low; last lia.
  rewrite /Z.sub -/(Z.pred (2 ^ Z.of_nat n)) -Z.ones_equiv.
  case: ltP => i_n.
  - apply: Z.ones_spec_low; lia.
  apply: Z.ones_spec_high; lia.
Qed.

Lemma wand_pow2nm1 sz (x: word sz) n :
  let: k := ((wsize_size_minus_1 sz).+1 - n)%nat in
  wand x (wrepr sz (2 ^ Z.of_nat n - 1)) = wshr (wshl x (Z.of_nat k)) (Z.of_nat k).
Proof.
  set k := (_ - _)%nat.
  have k_ge0 := Nat2Z.is_nonneg k.
  apply/eqP/eq_from_wbit_n => i.
  rewrite wandE wshrE // wshlE // wbit_n_pow2m1.
  have := ltn_ord i.
  move: (nat_of_ord i) => {}i i_bounded.
  replace (i < _)%nat with (i < n)%nat; last first.
  - apply Nat.min_case_strong => //  n_large.
    rewrite i_bounded.
    apply/ltP.
    move/ltP: i_bounded.
    lia.
  move: i_bounded.
  subst k.
  move: (wsize_size_minus_1 _) => w.
  rewrite ltnS => /leP i_bounded.
  rewrite Nat2Z.id.
  case: ltP => i_n.
  - rewrite (andbC (_ && _)); congr andb.
    + congr (wbit_n x); lia.
    symmetry; apply/andP; split; apply/leP; lia.
  rewrite andbF.
  replace (w.+1 - n + i <= w)%nat with false; first by rewrite andbF.
  symmetry; apply/leP.
  lia.
Qed.

Section FORALL_NAT_BELOW.
  Context (P: nat → bool).

  Fixpoint forallnat_below (n: nat) : bool :=
    if n is S n' then if P n' then forallnat_below n' else false else true.

  Lemma forallnat_belowP n :
    reflect (∀ i, (i < n)%coq_nat → P i) (forallnat_below n).
  Proof.
    elim: n.
    - by constructor => i /Nat.nlt_0_r.
    move => n ih /=; case hn: P; last first.
    - constructor => /(_ n (Nat.lt_succ_diag_r n)).
      by rewrite hn.
    case: ih => ih; constructor.
    - move => i i_le_n.
      case: (i =P n); first by move => ->.
      move => i_neq_n; apply: ih; lia.
    move => K; apply: ih => i i_lt_n; apply: K; lia.
  Qed.

End FORALL_NAT_BELOW.

Lemma wbit_n_Npow2n sz n (i: 'I_(wsize_size_minus_1 sz).+1) :
  wbit_n (wrepr sz (-2 ^ Z.of_nat n)) i = (n <= i)%nat.
Proof.
  move: (i: nat) (ltn_ord i) => {}i /ltP i_bounded.
  case: (@ltP n (wsize_size_minus_1 sz).+1) => hn.
  + apply/eqP.
    apply/forallnat_belowP: i i_bounded.
    change (
        let k := wrepr sz (- 2 ^ Z.of_nat n) in
        forallnat_below (λ i : nat, wbit_n k i == (n <= i)%nat) (wsize_size_minus_1 sz).+1
      ).
    apply/forallnat_belowP: n hn.
    by case: sz; vm_cast_no_check (erefl true).
  replace (wrepr _ _) with (0%R : word sz).
  rewrite w0E; symmetry; apply/leP; lia.
  rewrite wrepr_opp -oppr0.
  congr (-_)%R.
  apply/word_eqP.
  rewrite mkword_valK.
  apply/eqP; symmetry.
  rewrite /modulus two_power_nat_equiv.
  apply/Z.mod_divide; first exact: pow2nz.
  exists (2 ^ (Z.of_nat (n - (wsize_size_minus_1 sz).+1))).
  rewrite -Z.pow_add_r;
  first congr (2 ^ _).
  all: lia.
Qed.

Lemma wand_Npow2n sz (x: word sz) n :
  wand x (wrepr sz (- 2 ^ Z.of_nat n)) = wshl (wshr x (Z.of_nat n)) (Z.of_nat n).
Proof.
  apply/eqP/eq_from_wbit_n => i.
  have n_ge0 := Nat2Z.is_nonneg n.
  rewrite wandE wshlE // wshrE // Nat2Z.id wbit_n_Npow2n.
  move: (nat_of_ord i) (ltn_ord i) => {}i.
  rewrite ltnS => i_bounded.
  rewrite i_bounded andbT andbC.
  case: (@leP n i) => hni //=.
  congr (wbit_n x).
  lia.
Qed.

Lemma an_mod_bn_divn (a b n: Z) :
  n ≠ 0 →
  a * n mod (b * n) / n = a mod b.
Proof.
  by move => nnz; rewrite Zmult_mod_distr_r Z.div_mul.
Qed.

Lemma wand_modulo sz (x: word sz) n :
  wunsigned (wand x (wrepr sz (2 ^ Z.of_nat n - 1))) = wunsigned x mod 2 ^ Z.of_nat n.
Proof.
  rewrite wand_pow2nm1 wunsigned_wshr wunsigned_wshl /wbase /modulus two_power_nat_equiv.
  case: (@leP n (wsize_size_minus_1 sz).+1); last first.
  - move => k_lt_n.
    replace (_.+1 - n)%nat with 0%nat by lia.
    have [ x_pos x_bounded ] := wunsigned_range x.
    rewrite Z.mul_1_r Z.div_1_r !Z.mod_small //; split.
    1, 3: lia.
    + apply: Z.lt_trans; first exact: x_bounded.
      rewrite /wbase /modulus two_power_nat_equiv.
      apply: Z.pow_lt_mono_r; lia.
      by rewrite -two_power_nat_equiv.
  set k := _.+1.
  move => n_le_k.
  have := an_mod_bn_divn (wunsigned x) (2 ^ Z.of_nat n) (@pow2nz (k - n)%nat).
  rewrite -Z.pow_add_r.
  2-3: lia.
  replace (Z.of_nat n + Z.of_nat (k - n)) with (Z.of_nat k) by lia.
  done.
Qed.

Lemma div_mul_in_range a b m :
  0 < b →
  0 <= a < m →
  0 <= a / b * b < m.
Proof.
  move => b_pos a_range; split.
  * suff : 0 <= a / b by nia.
    apply: Z.div_pos; lia.
  elim_div; lia.
Qed.

Lemma wand_align sz (x: word sz) n :
  wunsigned (wand x (wrepr sz (-2 ^ Z.of_nat n))) = wunsigned x / 2 ^ Z.of_nat n * 2 ^ Z.of_nat n.
Proof.
  rewrite wand_Npow2n wunsigned_wshl wunsigned_wshr.
  apply: Z.mod_small.
  apply: div_mul_in_range.
  - exact: pow2pos.
  exact: wunsigned_range.
Qed.

(** Round to the multiple of [sz'] below. *)
Definition align_word (sz sz': wsize) (p: word sz) : word sz :=
  wand p (wrepr sz (-wsize_size sz')).

Lemma align_word_aligned (sz sz': wsize) (p: word sz) :
  wunsigned (align_word sz' p) mod wsize_size sz' == 0.
Proof.
  rewrite /align_word wsize_size_is_pow2 wand_align Z.mod_mul //.
  exact: pow2nz.
Qed.

Lemma align_word_range sz sz' (p: word sz) :
  wunsigned p - wsize_size sz' < wunsigned (align_word sz' p) <= wunsigned p.
Proof.
  rewrite /align_word wsize_size_is_pow2 wand_align.
  have ? := wunsigned_range p.
  have ? := pow2pos (wsize_log2 sz').
  elim_div; lia.
Qed.

Lemma align_wordE sz sz' (p: word sz) :
  wunsigned (align_word sz' p) = wunsigned p - (wunsigned p mod wsize_size sz').
Proof.
  have nz := wsize_size_pos sz'.
  rewrite {1}(Z.div_mod (wunsigned p) (wsize_size sz')); last lia.
  rewrite /align_word wsize_size_is_pow2 wand_align.
  lia.
Qed.

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

Definition word_uincl sz1 sz2 (w1:word sz1) (w2:word sz2) :=
  (sz1 <= sz2)%CMP && (w1 == zero_extend sz1 w2).

Lemma word_uincl_refl s (w : word s): word_uincl w w.
Proof. by rewrite /word_uincl zero_extend_u cmp_le_refl eqxx. Qed.
#[global]
Hint Resolve word_uincl_refl : core.

Lemma word_uincl_trans s2 w2 s1 s3 w1 w3 :
   @word_uincl s1 s2 w1 w2 -> @word_uincl s2 s3 w2 w3 -> word_uincl w1 w3.
Proof.
  rewrite /word_uincl => /andP [hle1 /eqP ->] /andP [hle2 /eqP ->].
  by rewrite (cmp_le_trans hle1 hle2) zero_extend_idem // eqxx.
Qed.

Lemma word_uincl_truncate sz1 (w1: word sz1) sz2 (w2: word sz2) sz w:
  word_uincl w1 w2 -> truncate_word sz w1 = ok w -> truncate_word sz w2 = ok w.
Proof.
  rewrite /word_uincl => /andP[hc1 /eqP ->] /truncate_wordP[hc2 ->].
  rewrite (zero_extend_idem _ hc2) truncate_word_le //.
  exact: (cmp_le_trans hc2 hc1).
Qed.

(* -------------------------------------------------------------------- *)
(* TODO_ARM: Move? *)

(* -------------------------------------------------------------------- *)

Notation pointer := (word Uptr) (only parsing).

(* ----------------------------------------------- *)

Definition in_uint_range (sz : wsize) z : bool :=
  (0 <=? z) && (z <=? wmax_unsigned sz).

Definition in_sint_range (sz : wsize) z : bool :=
  (wmin_signed sz <=? z) && (z <=? wmax_signed sz).

Definition signed {A:Type} (fu fs:A) s :=
  match s with
  | Unsigned => fu
  | Signed => fs
  end.

Definition in_wint_range (s : signedness) (sz : wsize) z :=
   assert (signed in_uint_range in_sint_range s sz z) ErrArith.

Definition wint_of_int (s : signedness) (sz : wsize) (z : Z) :=
  Let _ := in_wint_range s sz z in
  ok (wrepr sz z).

Definition int_of_word (s : signedness) (sz : wsize) (w : word sz) :=
  signed wunsigned wsigned s w.

Definition sem_word_extend (s : signedness) (szo szi : wsize) :=
  signed (@zero_extend szo szi) (@sign_extend szo szi) s.

