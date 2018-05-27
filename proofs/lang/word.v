(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Machine word *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ word.
Require ssrring.
Require Zquot.
Require Import Psatz ZArith utils type.
Import Utf8.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope Z_scope.

Ltac elim_div :=
   unfold Zdiv, Zmod;
     match goal with
       |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
       |  |-  context[ Zdiv_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
     end; unfold Remainder.

Lemma mod_pq_mod_q x p q :
  0 < p → 0 < q →
  (x mod (p * q)) mod q = x mod q.
Proof.
move => hzp hzq.
have hq : q ≠ 0 by nia.
have hpq : p * q ≠ 0 by nia.
elim_div => /(_ hq); elim_div => /(_ hpq) => [] [?] hr1 [?] hr2; subst.
elim_div => /(_ hq) [heq hr3].
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

Definition wsize_bits (s:wsize) : Z :=
  Zpos (Pos.of_succ_nat (wsize_size_minus_1 s)).

Definition wsize_size (sz: wsize) : Z :=
  wsize_bits sz / 8.

Lemma wsize_size_pos sz :
  0 < wsize_size sz.
Proof. by case sz. Qed.

Lemma wsize_cmpP sz sz' :
  wsize_cmp sz sz' = Nat.compare (wsize_size_minus_1 sz) (wsize_size_minus_1 sz').
Proof. by case: sz sz' => -[]; vm_compute. Qed.

Lemma wsize_size_m s s' :
  (s ≤ s')%CMP →
  wsize_size_minus_1 s ≤ wsize_size_minus_1 s'.
Proof.
by move=> /eqP; rewrite /cmp_le /gcmp wsize_cmpP Nat.compare_ge_iff.
Qed.

Definition word := fun sz =>
  [comRingType of (wsize_size_minus_1 sz).+1.-word].

Global Opaque word.

Definition wand {s} (x y: word s) : word s := wand x y.
Definition wor {s} (x y: word s) : word s := wor x y.
Definition wxor {s} (x y: word s) : word s := wxor x y.

Definition wlt {sz} (sg: signedness) : word sz → word sz → bool :=
  match sg with
  | Unsigned => λ x y, (urepr x < urepr y)%R
  | Signed => λ x y, (srepr x < srepr y)%R
  end.

Definition wle sz (sg: signedness) : word sz → word sz → bool :=
  match sg with
  | Unsigned => λ x y, (urepr x <= urepr y)%R
  | Signed => λ x y, (srepr x <= srepr y)%R
  end.

Definition wnot sz (w: word sz) : word sz :=
  wxor w (-1)%R.

Arguments wnot {sz} w.

Definition wbase (s: wsize) : Z :=
  modulus (wsize_size_minus_1 s).+1.

Definition wunsigned {s} (w: word s) : Z :=
  urepr w.

Definition wsigned {s} (w: word s) : Z :=
  srepr w.

Definition wrepr s (z: Z) : word s :=
  mkword (wsize_size_minus_1 s).+1 z.

Lemma word_ext n x y h h' :
  x = y →
  @mkWord n x h = @mkWord n y h'.
Proof. by move => e; apply/val_eqP/eqP. Qed.

Lemma wunsigned_inj sz : injective (@wunsigned sz).
Proof. by move => x y /eqP /val_eqP. Qed.

Lemma wrepr_unsigned s (w: word s) : wrepr s (wunsigned w) = w.
Proof. by rewrite /wrepr /wunsigned ureprK. Qed.

Lemma wrepr_signed s (w: word s) : wrepr s (wsigned w) = w.
Proof. by rewrite /wrepr /wsigned sreprK. Qed.

Lemma wunsigned_repr s z :
  wunsigned (wrepr s z) = z mod modulus (wsize_size_minus_1 s).+1.
Proof. done. Qed.

Lemma wunsigned_range sz (p: word sz) :
  0 <= wunsigned p < wbase sz.
Proof. by have /iswordZP := isword_word p. Qed.

Lemma wunsigned_add sz (p: word sz) (n: Z) :
  0 <= wunsigned p + n < wbase sz →
  wunsigned (p + wrepr sz n) = wunsigned p + n.
Proof.
case: p => p i h.
change (toword (add_word (mkWord i) (wrepr sz n)) = p + n).
rewrite/add_word mkwordK/= /urepr/=.
rewrite Zplus_mod_idemp_r.
exact: Zmod_small.
Qed.

Lemma wlt_irrefl sz sg (w: word sz) :
  wlt sg w w = false.
Proof. case: sg; exact: Z.ltb_irrefl. Qed.

Lemma wle_refl sz sg (w: word sz) :
  wle sg w w = true.
Proof. case: sg; exact: Z.leb_refl. Qed.

Definition wshr sz (x: word sz) (n: Z) : word sz :=
  lsr x (Z.to_nat n).

Definition wshl sz (x: word sz) (n: Z) : word sz :=
  lsl x (Z.to_nat n).

Definition wsar sz (x: word sz) (n: Z) : word sz :=
  asr x (Z.to_nat n).

Definition wmulhu sz (x y: word sz) : word sz :=
  wrepr sz ((wunsigned x * wunsigned y) / wbase sz).

Definition wmulhs sz (x y: word sz) : word sz :=
  wrepr sz ((wsigned x * wsigned y) / wbase sz).

Lemma wmulhuE sz (x y: word sz) : wmulhu x y = wrepr sz (wunsigned x * wunsigned y ÷ wbase sz).
Proof.
    rewrite /wmulhu Zquot.Zquot_Zdiv_pos //.
    apply: Z.mul_nonneg_nonneg; apply: (proj1 (wunsigned_range _)).
Qed.

Definition wmax_unsigned sz := wbase sz - 1.
Definition wmin_signed (sz: wsize) : Z := - modulus (wsize_size_minus_1 sz).
Definition wmax_signed (sz: wsize) : Z := modulus (wsize_size_minus_1 sz) - 1.

Notation u8   := (word U8).
Notation u16  := (word U16).
Notation u32  := (word U32).
Notation u64  := (word U64).
Notation u128 := (word U128).
Notation u256 := (word U256).

Definition x86_shift_mask (s:wsize) : u8 :=
  match s with 
  | U8 | U16 | U32 => wrepr U8 31
  | U64  => wrepr U8 63
  | U128 => wrepr U8 127
  | U256 => wrepr U8 255
  end%Z.

Definition wbit_n sz (w:word sz) (n:nat) : bool := 
   wbit (wunsigned w) n.

Lemma eq_from_wbit_n s (w1 w2: word s) :
  reflect (∀ i : 'I_(wsize_size_minus_1 s).+1, wbit_n w1 i = wbit_n w2 i) (w1 == w2).
Proof. apply/eq_from_wbit. Qed.

Lemma wandE s (w1 w2: word s) i :
  wbit_n (wand w1 w2) i = wbit_n w1 i && wbit_n w2 i.
Proof. by rewrite /wbit_n /wand wandE. Qed.

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

Lemma wshlE sz (w: word sz) c i :
  wbit_n (wshl w c) i = (Z.to_nat c <= i <= wsize_size_minus_1 sz)%nat && wbit_n w (i - Z.to_nat c).
Proof.
  rewrite /wbit_n /wshl /=.
  case: leP => hic /=;
    last (rewrite wbit_lsl_lo //; apply/leP; lia).
  have eqi : (Z.to_nat c + (i - Z.to_nat c))%nat = i.
   * by rewrite /addn /addn_rec; zify; rewrite Nat2Z.inj_sub; lia.
  have := wbit_lsl w (Z.to_nat c) (i - Z.to_nat c).
  by rewrite eqi => ->.
Qed.

Lemma wshl_ovf sz (w: word sz) c :
  (wsize_size_minus_1 sz < Z.to_nat c)%coq_nat →
  wshl w c = 0%R.
Proof.
  move => hc; apply/eqP/eq_from_wbit_n => i.
  rewrite wshlE {2}/wbit_n wbit0.
  case: i => i /= /leP /le_S_n hi.
  have /leP -> := hi.
  case: leP => //; lia.
Qed.

Definition lsb {s} (w: word s) : bool := wbit_n w 0.
Definition msb {s} (w: word s) : bool := wbit_n w (wsize_size_minus_1 s).

Definition wdwordu sz (hi lo: word sz) : Z :=
  wunsigned hi * wbase sz + wunsigned lo.

Definition wdwords sz (hi lo: word sz) : Z :=
  wsigned hi * wbase sz + wunsigned lo.

Definition waddcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x + wunsigned y + Z.b2z c in
  (wbase sz <=? n, wrepr sz n).

Definition wsubcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x - wunsigned y - Z.b2z c in
  (n <? 0, wrepr sz n).

Definition wumul sz (x y: word sz) :=
  let n := wunsigned x * wunsigned y in
  (wrepr sz (Z.quot n (wbase sz)), wrepr sz n).

Definition zero_extend sz sz' (w: word sz') : word sz :=
  wrepr sz (wunsigned w).

Definition sign_extend sz sz' (w: word sz') : word sz :=
  wrepr sz (wsigned w).

Definition wbit sz (w i: word sz) : bool :=
  wbit_n w (Z.to_nat (wunsigned i mod wsize_bits sz)).

Definition wror sz (w:word sz) (z:Z) := 
  let i := z mod wsize_bits sz in
  wor (wshr w i) (wshl w (wsize_bits sz - i)).

Definition wrol sz (w:word sz) (z:Z) := 
  let i := z mod wsize_bits sz in
  wor (wshl w i) (wshr w (wsize_bits sz - i)).

(* -------------------------------------------------------------------*)
Lemma msb0 sz : @msb sz 0 = false.
Proof. by case: sz. Qed.

Lemma wshr0 sz (w: word sz) : wshr w 0 = w.
Proof. by rewrite /wshr /lsr Z.shiftr_0_r ureprK. Qed.

Lemma wshl0 sz (w: word sz) : wshl w 0 = w.
Proof. by rewrite /wshl /lsl Z.shiftl_0_r ureprK. Qed.

Lemma wsar0 sz (w: word sz) : wsar w 0 = w.
Proof. by rewrite /wsar /asr Z.shiftr_0_r sreprK. Qed.

(* -------------------------------------------------------------------*)
Lemma wltuE' sz (α β: word sz) :
  wlt Unsigned α β = (wunsigned (β - α) == (wunsigned β - wunsigned α)%Z) && (β != α).
Proof.
by rewrite -[X in X && _]negbK -wltuE /= -lerNgt andbC eq_sym -ltr_neqAle.
Qed.

Lemma wleuE sz (w1 w2: word sz) :
  wle Unsigned w1 w2 = (wunsigned (w2 - w1) == (wunsigned w2 - wunsigned w1))%Z.
Proof.
rewrite /= ler_eqVlt -/(wlt Unsigned _ _) wltuE'.
rewrite orb_andr /= [w2 == w1]eq_sym orbN andbT.
by rewrite orb_idl // => /eqP /val_inj ->; rewrite subZE !subrr.
Qed.

Lemma wltsE sz (α β: word sz) :
  α ≠ β → wlt Signed α β = (msb (α - β) != (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof. Admitted.

Lemma wltsE' sz (α β: word sz) :
  α ≠ β → wlt Signed β α = (msb (α - β) == (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof. Admitted.

Lemma wlesE sz (α β: word sz) :
  α ≠ β → wle Signed β α = (msb (α - β) == (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof. Admitted.

Lemma wlesE' sz (α β: word sz) :
  α ≠ β → wle Signed α β = (msb (α - β) != (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof. Admitted.

(* -------------------------------------------------------------------*)
Lemma zero_extend0 sz sz' :
  @zero_extend sz sz' 0%R = 0%R.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma zero_extend_u sz (w:word sz) : zero_extend sz w = w.
Proof. by rewrite /zero_extend wrepr_unsigned. Qed.

Lemma zero_extend_sign_extend sz sz' s (w: word s) :
 (sz ≤ sz')%CMP →
  zero_extend sz (sign_extend sz' w) = sign_extend sz w.
Proof.
move => hsz; rewrite /sign_extend; apply: word_ext.
move: (wsigned w) => {w} z.
rewrite wunsigned_repr.
case: (modulus_m (wsize_size_m hsz)) => n hn.
by rewrite hn mod_pq_mod_q.
Qed.

Lemma zero_extend_wrepr sz sz' z :
  (sz <= sz')%CMP →
  zero_extend sz (wrepr sz' z) = wrepr sz z.
Proof.
move/wsize_size_m => hle.
apply: word_ext.
rewrite /wunsigned /urepr /wrepr /=.
case: (modulus_m hle) => n -> {hle}.
exact: mod_pq_mod_q.
Qed.

Lemma zero_extend_idem s s1 s2 (w:word s) : 
  (s1 <= s2)%CMP -> zero_extend s1 (zero_extend s2 w) = zero_extend s1 w.
Proof.
  by move=> hle;rewrite [X in (zero_extend _ X) = _]/zero_extend zero_extend_wrepr.
Qed.

Lemma wbit_zero_extend s s' (w: word s') i :
  wbit_n (zero_extend s w) i = (i <= wsize_size_minus_1 s)%nat && wbit_n w i.
Proof.
rewrite /zero_extend /wbit_n /wunsigned /wrepr.
move: (urepr w) => {w} z.
rewrite mkwordK.
set m := wsize_size_minus_1 _.
rewrite /CoqWord.word.wbit /=.
rewrite /modulus two_power_nat_equiv.
case: leP => hi.
+ rewrite Z.mod_pow2_bits_low //; lia.
rewrite Z.mod_pow2_bits_high //; lia.
Qed.

Lemma wbit_sign_extend s s' (w: word s') i :
  wbit_n (sign_extend s w) i = wbit_n w (min i (wsize_size_minus_1 s)).
Proof. Admitted.

Lemma sign_zero_sign_extend sz sz' (w: word sz') :
  sign_extend sz (zero_extend sz' (sign_extend sz w)) = sign_extend sz w.
Proof.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_sign_extend, wbit_zero_extend) -Min.min_assoc Min.min_idempotent.
case: leP => //= /Nat.nle_gt hlt; rewrite /wbit_n wbit_word_ovf //.
exact/ltP.
Qed.

Lemma sign_extend_u sz (w: word sz) : sign_extend sz w = w.
Proof. exact: sreprK. Qed.

Lemma wrepr0 sz : wrepr sz 0 = 0%R.
Proof. by apply/eqP. Qed.

Lemma wsigned0 sz : @wsigned sz 0%R = 0%Z.
Proof. by case: sz. Qed.

Lemma sign_extend0 sz sz' :
  @sign_extend sz sz' 0%R = 0%R.
Proof. by rewrite /sign_extend wsigned0 wrepr0. Qed.

Lemma wandC sz : commutative (@wand sz).
Proof.
  by move => x y; apply/eqP/eq_from_wbit => i;
  rewrite /wand !CoqWord.word.wandE andbC.
Qed.

Lemma wand0 sz (x: word sz) : wand 0 x = 0%R.
Proof. by apply/eqP. Qed.

Lemma wxor0 sz (x: word sz) : wxor 0 x = x.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma wxor_xx sz (x: word sz) : wxor x x = 0%R.
Proof. by apply/eqP/eq_from_wbit; rewrite /= Z.lxor_nilpotent. Qed.

Lemma wrepr_add sz (x y: Z) :
  wrepr sz (x + y) = (wrepr sz x + wrepr sz y)%R.
Proof. by apply: word_ext; rewrite /wrepr !mkwordK Zplus_mod. Qed.

Lemma wrepr_sub sz (x y: Z) :
  wrepr sz (x - y) = (wrepr sz x - wrepr sz y)%R.
Proof. by apply: word_ext; rewrite /wrepr !mkwordK -Zminus_mod_idemp_r -Z.add_opp_r Zplus_mod. Qed.

Lemma wmulE sz (x y: word sz) : (x * y)%R = wrepr sz (wunsigned x * wunsigned y).
Proof. by rewrite /wunsigned /wrepr; apply: word_ext. Qed.

Lemma wrepr_mul sz (x y: Z) :
  wrepr sz (x * y) = (wrepr sz x * wrepr sz y)%R.
Proof. by apply: word_ext; rewrite /wrepr !mkwordK Zmult_mod. Qed.

Lemma wadd_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  (zero_extend sz x + zero_extend sz y)%R = zero_extend sz (x + y).
Proof.
move => hle; apply: word_ext.
rewrite /wrepr !mkwordK -Zplus_mod.
rewrite /wunsigned /urepr /=.
change (x + y)%R with (add_word x y).
rewrite /add_word /= /urepr /=.
case: (modulus_m (wsize_size_m hle)) => n -> {hle}.
by rewrite mod_pq_mod_q.
Qed.

Lemma wmul_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  (zero_extend sz x * zero_extend sz y)%R = zero_extend sz (x * y).
Proof.
move => hle; apply: word_ext.
rewrite /wrepr !mkwordK -Zmult_mod.
rewrite /wunsigned /urepr /=.
change (x * y)%R with (mul_word x y).
rewrite /mul_word /= /urepr /=.
case: (modulus_m (wsize_size_m hle)) => n -> {hle}.
by rewrite mod_pq_mod_q.
Qed.

Lemma zero_extend_wshl sz sz' (x: word sz') c :
  (sz ≤ sz')%CMP →
  zero_extend sz (wshl x c) = wshl (zero_extend sz x) c.
Proof.
move => hle; apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wshlE).
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
apply/leP; rewrite /subn /subn_rec; lia.
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

Lemma wxor_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  wxor (zero_extend sz x) (zero_extend sz y) = zero_extend sz (wxor x y).
Proof.
move => hle.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wxorE).
by case: (_ <= _)%nat.
Qed.

(* -------------------------------------------------------------------*)
Ltac wring := 
  rewrite ?zero_extend_u; ssrring.ssring.

(* -------------------------------------------------------------------*)
Definition check_scale (s:Z) :=
  (s == 1%Z) || (s == 2%Z) || (s == 4%Z) || (s == 8%Z).

(* -------------------------------------------------------------------*)
Definition mask_word (sz:wsize) : u64 := 
  match sz with
  | U8 | U16 => wshl (-1)%R (wsize_bits sz)
  | _ => 0%R
  end.

Definition merge_word (wr: u64) (sz:wsize) (w:word sz) := 
   wxor (wand (mask_word sz) wr) (zero_extend U64 w).

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
  move=> j; rewrite !subwordE; congr (CoqWord.word.wbit (t2w _) _).
  apply/val_eqP/eqP => /=; apply/eq_map=> k.
  suff ->: val wt = val w by done.
  by rewrite {}/wt; case: _ / sz_even.
rewrite {}eq_st wcat_subwordK {s t}/wt; case: _ / sz_even.
by rewrite /wrepr /= ureprK.
Qed.

(* -------------------------------------------------------------------*)
Definition lift1_vec ve (op : word ve -> word ve)
    (sz:wsize) (w:word sz) : word sz :=
  make_vec sz (map op (split_vec ve w)).
Arguments lift1_vec : clear implicits.

Definition lift2_vec ve (op : word ve -> word ve -> word ve)
  (sz:wsize) (w1 w2:word sz) : word sz :=
  make_vec sz (map2 op (split_vec ve w1) (split_vec ve w2)).
Arguments lift2_vec : clear implicits.

(* -------------------------------------------------------------------*)
Definition wpshufb1 (s : seq u8) (idx : u8) :=
  if msb idx then 0%R else
    let off := wunsigned (wand idx (wshl 1 4%Z - 1)) in
    (s`_(Z.to_nat off))%R.

Definition wpshufb (sz: wsize) (w idx: word sz) : word sz :=
  let s := split_vec 8 w in
  let i := split_vec 8 idx in
  let r := map (wpshufb1 s) i in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Definition wpshufd1 (s : u128) (o : u8) (i : nat) :=
  wshl s (32 * urepr (subword (2 * i) 2 o)).

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
Definition wpblendd sz (w1 w2: word sz) (m: u8) : word sz :=
  let v1 := split_vec U32 w1 in
  let v2 := split_vec U32 w2 in
  let b := split_vec 1 m in
  let r := map3 (λ b v1 v2, if b == 1%R then v2 else v1) b v1 v2 in
  make_vec sz r.
