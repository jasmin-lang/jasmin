require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.
require Modulo_ct.
import StdOrder.IntOrder Ring.IntID.

clone import Modulo_ct.T with
  theory LeakageModel <-  LeakageModelTV.

lemma leak_div_bound (w:W64.t) : 0 <= leak_div w <= 64.
proof. smt (lzcnt_size size_mkseq size_rev). qed.

lemma leak_div64 b: b <> W64.zero => leak_div b <> 64.
proof.
  apply contra; rewrite /leak_div => h.
  have := lzcnt_bound (w2bits b).
  rewrite W64.size_w2bits /= -W64.to_uintE W64.to_uint_eq /= h /#.
qed.

import BitEncoding.BS2Int.

lemma leak_div0 (x:W64.t) :  2^63 <= to_uint x <=> leak_div x = 0.
proof.
rewrite /leak_div W64.to_uintE /= W64.w2bitsE /=.
have := lzcnt_bound (mkseq ("_.[_]"x) 64).
rewrite size_mkseq /max /=.
case: (64 = lzcnt (rev (mkseq ("_.[_]" x) 64))) => [<- /= /#| hdiff].
case: (lzcnt (rev (mkseq ("_.[_]" x) 64)) = 0) => [-> /= [] // | ] /=.
pose n := lzcnt _; pose X := bs2int _.
move=> h0 h1; have /= /#: 2 ^ (64 - n) <= 2^63.
apply ler_weexpn2l => //. smt (lzcnt_size size_mkseq size_rev).
qed.

lemma shift_leak_div (b:W64.t) :
  b <> W64.zero =>
  to_uint (b `<<<` leak_div b) = to_uint b * 2 ^ leak_div b.
proof.
  move=> hz; rewrite W64.to_uint_shl. smt (leak_div_bound).
  rewrite modz_small 2://.
  split.
  + apply mulr_ge0; 1: smt(W64.to_uint_cmp).
    by apply expr_ge0.
  move=> _; rewrite W64.to_uintE.
  have := lzcnt_bound (w2bits b).
  rewrite /leak_div size_w2bits (eq_sym 64) leak_div64 //= => -[] _.
  rewrite -(ltr_pmul2r (2 ^ lzcnt (rev (w2bits b)))).
  + by apply expr_gt0.
  rewrite -exprD_nneg //; 1,2: smt(leak_div_bound).
  by rewrite subrK.
qed.

lemma shift_ZLCNT (b:W64.t) :
  b <> W64.zero =>
  to_uint (b `<<<` to_uint (LZCNT_64 b).`6) = to_uint b * 2 ^ leak_div b.
proof.
  rewrite /LZCNT_64 /= W64.to_uint_small; 1: smt (leak_div_bound); apply shift_leak_div.
qed.

lemma shift_zlcnt (b:W64.t) :
  b <> W64.zero =>
  2^63 <= to_uint (b `<<<` to_uint (LZCNT_64 b).`6) < 2^64.
proof.
  move=> hz; split; last first.
  + move=> _ /=; have /> := W64.to_uint_cmp ((b `<<<` to_uint (LZCNT_64 b).`6)).
  rewrite shift_ZLCNT 1://.
  have := lzcnt_bound (w2bits b).
  rewrite size_w2bits (eq_sym 64) leak_div64 1:// /= -W64.to_uintE => -[h1 _].
  move: h1.
  rewrite -(ler_pmul2r (2 ^ to_uint (W64.of_int (lzcnt (rev (w2bits b)))))).
  + by rewrite expr_gt0.
  rewrite -Domain.exprD_nneg; 1: smt(leak_div_bound leak_div64).
  + smt (W64.to_uint_cmp).
  rewrite W64.to_uint_small /=. smt (leak_div_bound ).
  have -> // : (63 - lzcnt (rev (w2bits b)) + lzcnt (rev (w2bits b))) = 63 by ring.
qed.

equiv l2 : M.mod_TV ~ M.mod_TV : ={M.leakages, b} /\ b{1} <> W64.zero ==> ={M.leakages}.
proof.
  proc; inline *; wp; skip => /> &1 &2.
  move: (b{2}) (a{1}) (a{2}) => b a1 a2 {&1 &2} hb.
  rewrite /leak_div_64 /leak_div_64_TV; congr.
  suff : forall a1,
   leak_div
     (if (if (LZCNT_64 a1).`5 then W64.one else if (LZCNT_64 b).`5 then W64.zero else W64.of_int 4660) = W64.zero then
     W64.of_int 18446744073709551615
   else
     if (if (LZCNT_64 a1).`5 then W64.one else if (LZCNT_64 b).`5 then W64.zero else W64.of_int 4660) = W64.one then
       a1
     else
       if ! addc_carry (b `<<` truncateu8 (LEA_64 ((LZCNT_64 b).`6 - W64.one)) `<<` W8.one) a1 false then
         (addc (b `<<` truncateu8 (LEA_64 ((LZCNT_64 b).`6 - W64.one)) `<<` W8.one) a1 false).`2
       else LEA_64 ((b `<<` truncateu8 (LEA_64 ((LZCNT_64 b).`6 - W64.one))) + a1)) = 0.
   + by move=> h; rewrite !h.
  move=> {a1 a2} a1.
  case: (LZCNT_64 a1).`5 => hzcnta /=.
  + move: hzcnta.
    rewrite /LZCNT_64 /leak_div /ZF_of /= => h.
    have :  W64.to_uint (of_int (lzcnt (rev (w2bits a1))))%W64 = W64.to_uint W64.zero.
    + by rewrite h.
    rewrite /= W64.WRingA.oner_neq0 W64.to_uint_small //=.
    smt (lzcnt_size W64.size_w2bits size_rev).
  case: (LZCNT_64 b).`5 => hzcntb /=; 1: by apply leak_div0.
  rewrite !W64.to_uint_eq /= /LEA_64 /addc /carry_add /b2i /=.
  move: hzcntb; rewrite /LZCNT_64 /= /ZF_of => hzcntb.
  rewrite !/W64.(`<<`) !W8u8.to_uint_truncateu8.
  have hb_bound : 0 < leak_div b < 64 by smt (leak_div_bound leak_div64).
  have -> : 64 = 2^6 by done.
  rewrite !modz_dvd_pow 1,2:// !W64.to_uint_small 1:/#.
  rewrite modz_small /= 1:/# W64.shlw_add 1:/# 1:// /=.
  apply leak_div0.
  have heq: to_uint b * 2 ^ (leak_div b - 1) * 2 = to_uint b * 2 ^ leak_div b.
  + have {2}-> : 2 = 2 ^ 1 by done.
    rewrite mulzA -exprD_nneg //; 1: smt(leak_div_bound).
  have h :  to_uint (b `<<<` leak_div b - 1) * 2 = to_uint (b `<<<` leak_div b).
  + have := shift_zlcnt b hb.
    rewrite shift_ZLCNT 1:// shift_leak_div 1:// => h.
    rewrite W64.to_uint_shl; 1: smt (leak_div_bound).
    by rewrite modz_small //; move: heq h => /= /#.
  have /= h1 : W64.to_uint a1 < 2^63.
  + have := leak_div0 a1.
    move: hzcnta; rewrite /LZCNT_64 /ZF_of /= W64.to_uint_eq /= W64.to_uint_small 2:/#.
    smt (leak_div_bound).
  have := shift_zlcnt b hb.
  rewrite /LZCNT_64 /= W64.to_uint_small /=; 1: smt(leak_div_bound).
  move=> h2.
  case: (! 18446744073709551616 <= to_uint (b `<<<` lzcnt (rev (w2bits b))) + to_uint a1) => /= h3.
  + rewrite W64.to_uintD_small /= 1:/#; smt(W64.to_uint_cmp).
  rewrite W64.to_uintD_small /= 1:#smt:(leak_div_bound).
  smt (W64.to_uint_cmp).
qed.

lemma to_uint_lzcnt n : to_uint (of_int (lzcnt (rev (w2bits n))))%W64 = lzcnt (rev (w2bits n)).
proof.
  rewrite to_uint_small //.
  have := lzcnt_size (rev (w2bits n)).
  rewrite /= size_rev size_w2bits /#.
qed.

lemma lzcnt0E w :
    (LZCNT_64 w).`5 => 2^63 <= to_uint w < 2 ^ 64.
proof.
  rewrite /LZCNT_64 /ZF_of /= W64.to_uint_eq /= to_uint_lzcnt => w_big.
  have := lzcnt_bound (w2bits w).
  by rewrite w_big size_w2bits /= -to_uintE.
qed.

lemma lzcntn0E w :
    !(LZCNT_64 w).`5 => to_uint w < 2 ^ 63 /\ 1 <= lzcnt (rev (w2bits w)) <= 64.
proof.
  rewrite /LZCNT_64 /ZF_of /= W64.to_uint_eq /= to_uint_lzcnt => w_not_big.
  have := lzcnt_bound (w2bits w).
  have := lzcnt_size (rev (w2bits w)); rewrite size_rev size_w2bits -to_uintE.
  have /# := ler_weexpn2l 2 _ (64 - lzcnt (rev (w2bits w))) 63=> //.
qed.

hoare mod_TV_correct x y : M.mod_TV : arg = (x, y) /\ y <> W64.zero ==> res = x \umod y.
proof.
  proc.
  inline *; wp; skip => /> y_nz.
  case: (LZCNT_64 x).`5.
  + by move => /> _; rewrite W64.WRingA.oner_neq0.
  move => /lzcntn0E[] x_not_big _.
  case: (LZCNT_64 y).`5.
  + move => /> /lzcnt0E y_big.
    rewrite umodE /ulift2 /= modz_small ?to_uintK 2://; smt(W64.to_uint_cmp).
  move => /lzcntn0E[] y_not_big y_lzcnt_range.
  rewrite !W64.to_uint_eq /= /LEA_64 /addc /carry_add /b2i /=.
  rewrite !/W64.(`<<`) W64.shlw_add 2://; 1: smt(W64.to_uint_cmp).
  rewrite /LZCNT_64 /truncateu8 /=.
  rewrite modz_dvd 1://.
  rewrite to_uint_small; 1: smt (lzcnt_size size_rev size_w2bits).
  rewrite (modz_small _ 64) /=; 1: smt (lzcnt_size size_rev size_w2bits).
  have heq: to_uint y * 2 ^ (leak_div y - 1) * 2 = to_uint y * 2 ^ leak_div y.
  + have {2}-> : 2 = 2 ^ 1 by done.
    rewrite mulzA -exprD_nneg //; 1: smt(leak_div_bound).
  have heq1 :  to_uint (y `<<<` leak_div y) = to_uint y * 2 ^ leak_div y.
  + by rewrite -(shift_ZLCNT y y_nz) /LZCNT_64 /= to_uint_lzcnt.
  have heq2 :  to_uint (y `<<<` leak_div y - 1) = to_uint y * 2 ^ (leak_div y - 1).
  + have := shift_zlcnt y y_nz.
    rewrite shift_ZLCNT 1:// => h.
    rewrite W64.to_uint_shl; 1: smt (leak_div_bound).
    by rewrite modz_small //; move: heq h => /= /#.
  have := shift_zlcnt y y_nz.
  move: y_lzcnt_range x_not_big y_not_big; rewrite /LZCNT_64 /=  -/(leak_div y).
  move => y_lzcnt_range x_not_big y_not_big.
  rewrite W64.to_uint_small 1:/# => h1.
  case: (18446744073709551616 <= to_uint (y `<<<` leak_div y) + to_uint x) => /= c;
    rewrite umodE /ulift2 to_uintD_small 1:/#.
  + by rewrite heq2 mulzC modzMDl.
  by rewrite heq1 mulzC modzMDl.
qed.
