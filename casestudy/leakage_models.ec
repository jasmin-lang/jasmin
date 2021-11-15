require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

(* Leakage models BL, TV, CL, and TV+CL and common lemmas for the verification of the copy-mac implementations. *)

theory LeakageModelBL.
op leak_mem (a: address) : address = a.
op leak_div_32 (a b: W32.t) : address list = [].
op leak_div_64 (a b: W64.t) : address list = [].
end LeakageModelBL.

op leak_div (a: W32.t) : int =
  lzcnt (rev (w2bits a)).

theory LeakageModelTV.

op leak_div_32 (a b: W32.t) : address list =
[ leak_div a ; to_uint b ].

op leak_div_64 (a b: W64.t) : address list =
[ to_uint a ; to_uint b ].

op leak_mem = LeakageModelBL.leak_mem.

end LeakageModelTV.

theory LeakageModelCL.

op leak_div_32 = LeakageModelBL.leak_div_32.
op leak_div_64 = LeakageModelBL.leak_div_64.

op leak_mem (a: address) : address =
  a %/ 64.

end LeakageModelCL.

theory LeakageModelTVCL.
op leak_div_32 = LeakageModelTV.leak_div_32.
op leak_div_64 = LeakageModelTV.leak_div_64.
op leak_mem = LeakageModelCL.leak_mem.
end LeakageModelTVCL.

lemma leak_div_or (x y : W32.t) : leak_div (x `|` y) = min (leak_div x) (leak_div y).
    proof.
      rewrite /leak_div /w2bits.
      elim/natind: 32.
      + by move=> n hn; rewrite !mkseq0_le 1..3:// /= rev_nil.
    move=> n hn hrec; rewrite !mkseqS 1..3:// !rev_rcons /= hrec; smt(lzcnt_size).
  qed.

lemma leak_div_bound (w:W32.t) : 0 <= leak_div w <= 32.
    proof. smt (lzcnt_size size_mkseq size_rev). qed.

lemma nosmt ltr_weexpn2l x m n:
    2 <= x => 0 <= m => 0 <= n =>
    m < n <=> x ^ m < x ^ n.
    proof.
    move=> h1 h2 h3; case: (m < n) => /= h4.
      + have -> : n = (n - m) + m by ring.
      rewrite Ring.IntID.exprD_nneg 1:/# 1://.
      rewrite -{1}(Ring.IntID.div1r (x^m)).
      rewrite StdOrder.IntOrder.ltr_pmul2r.
      + smt (StdOrder.IntOrder.expr_gt0).
      smt (StdOrder.IntOrder.exprn_egt1).
      have -> : m = (m - n) + n by ring.
      rewrite Ring.IntID.exprD_nneg 1:/# 1:// -lezNgt.
      rewrite -{1}(Ring.IntID.div1r (x^n)).
      rewrite StdOrder.IntOrder.ler_pmul2r.
      + smt (StdOrder.IntOrder.expr_gt0).
      smt (StdOrder.IntOrder.exprn_ege1).
  qed.

lemma leak_div_le (w1 w2: W32.t) : to_uint w1 <= to_uint w2 => leak_div w2 <= leak_div w1.
    proof.
      rewrite W32.to_uintE /leak_div.
      have := lzcnt_bound (w2bits w1).
      have := lzcnt_bound (w2bits w2).
      rewrite !size_w2bits => h1 h2 h3.
      have : (if 32 = lzcnt (rev (w2bits w1)) then 0 else 2 ^ (32 - lzcnt (rev (w2bits w1)) - 1)) <
      2 ^ (32 - lzcnt (rev (w2bits w2))) by smt().
    case (32 = lzcnt (rev (w2bits w1))) => /= [ <- | ] h; 1: smt (leak_div_bound).
      rewrite -ltr_weexpn2l 1://; smt(leak_div_bound).
  qed.

(* Remark: the shift by 23 look arbitrary. I think a shift by 8 is suffisant *)
lemma l_rotate_offset_div_core (x md_size : W32.t) :
  0 <= to_uint x < 2^8 =>
  16 <= to_uint md_size <= 64 =>
  leak_div (x + (md_size `<<` W8.of_int 23)) = leak_div (md_size `<<` W8.of_int 23).
proof.
  move=> /= h1 h2.
  pose md23 := md_size `<<` W8.of_int 23.
  rewrite -(W32.orw_disjoint _ md23).
  + apply W32.wordP => i hi; rewrite W32.zerowE W32.andwE.
    rewrite !W32.get_to_uint hi /=.
    case: (i < 8) => hi'.
    + rewrite /md23 /(`<<`) /= W32.to_uint_shl 1:// IntDiv.modz_pow2_div.
      + by apply StdOrder.IntOrder.divr_ge0; 1: smt(W32.to_uint_cmp).
      + smt().
      have h21 : 2 = 2 ^ 1 by done.
      rewrite {6}h21 modz_dvd_pow 1:/#.
      have -> : 2 ^ 23 = 2 ^ (23 - i - 1) * 2 * 2 ^ i.
      + by rewrite {3}h21 -!Ring.IntID.exprD_nneg 1,3,4:/# 1://; congr; ring.
      rewrite -(mulzA (W32.to_uint _)) mulzK; 1: smt(gt0_pow2).
      by rewrite -mulzA modzMl.
    rewrite divz_small //.
    by have /= /# :=StdOrder.IntOrder.ler_weexpn2l 2 _ 8 i.
  rewrite leak_div_or.
  have : leak_div (W32.of_int 256) <= leak_div x.
  + by apply leak_div_le => /= /#.
  have -> : leak_div (W32.of_int 256) = 23.
  + by rewrite /leak_div /w2bits /mkseq -iotaredE /= !W32.of_intwE; cbv delta.
  have : leak_div md23 <= leak_div (W32.of_int (2^23)).
  + by apply leak_div_le; rewrite /md23 /(`<<`) /= !W32.to_uint_shl //= modz_small /#.
  have -> /# : leak_div (W32.of_int (2^23)) = 8.
  by rewrite /leak_div /w2bits /mkseq -iotaredE /= !W32.of_intwE; cbv delta.
qed.
