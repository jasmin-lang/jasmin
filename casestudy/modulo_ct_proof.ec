require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require Modulo_ct.

op leak_div (a: W64.t) : int =
  lzcnt (rev (w2bits a)).

theory LeakageModelDiv.

op leak_div_64 (a b: W64.t) : address list =
  [ leak_div a ; to_uint b ].

op leak_mem (a: W64.t) : address = witness.

end LeakageModelDiv.

clone import Modulo_ct.T with
  theory LeakageModel <- LeakageModelDiv.

lemma leak_div_bound (w:W64.t) : 0 <= leak_div w <= 64.
proof. smt (lzcnt_size size_mkseq size_rev). qed.

lemma leak_div64 b: b <> W64.zero => leak_div b <> 64.
proof.
  apply contra; rewrite /leak_div => h.
  have := lzcnt_bound (w2bits b).
  rewrite h W64.size_w2bits /= -W64.to_uintE W64.to_uint_eq /= /#.
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
apply StdOrder.IntOrder.ler_weexpn2l => //. smt (lzcnt_size size_mkseq size_rev).
qed.

lemma add_lt (x y: W64.t) : !(x + y \ult x) <=> (to_uint x + to_uint y < W64.modulus).
proof.
  rewrite ultE W64.to_uintD.
  move: (W64.to_uint_cmp x) (W64.to_uint_cmp y) => /= hx hy /#.
qed.

lemma add_le (x y: W64.t) : (x + y \ult x) <=> (to_uint (x + y) = to_uint x + to_uint y - W64.modulus).
proof.
  rewrite ultE W64.to_uintD.
  move: (W64.to_uint_cmp x) (W64.to_uint_cmp y) => /= hx hy /#.
qed.

lemma shift_leak_div (b:W64.t) : 
  b <> W64.zero => 
  to_uint (b `<<<` leak_div b) = to_uint b * 2 ^ leak_div b.
proof.
  move=> hz; rewrite W64.to_uint_shl. smt (leak_div_bound).
  rewrite modz_small 2://. 
  split.
  + apply StdOrder.IntOrder.mulr_ge0; 1: smt(W64.to_uint_cmp).
    by apply StdOrder.IntOrder.expr_ge0.
  move=> _; rewrite W64.to_uintE.
  have := lzcnt_bound (w2bits b).
  rewrite /leak_div size_w2bits (eq_sym 64) leak_div64 //= => -[] _. 
  rewrite -(StdOrder.IntOrder.ltr_pmul2r (2 ^ lzcnt (rev (w2bits b)))).
  + by apply StdOrder.IntOrder.expr_gt0.
  rewrite -Ring.IntID.exprD_nneg //; 1,2: smt(leak_div_bound).
  by rewrite Ring.IntID.subrK.
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
  rewrite -(StdOrder.IntOrder.ler_pmul2r (2 ^ to_uint (W64.of_int (lzcnt (rev (w2bits b)))))).
  + by rewrite StdOrder.IntOrder.expr_gt0.
  rewrite -StdOrder.IntOrder.Domain.exprD_nneg; 1: smt(leak_div_bound leak_div64).
  + smt (W64.to_uint_cmp).
  rewrite W64.to_uint_small /=. smt (leak_div_bound ).
  have -> // : (63 - lzcnt (rev (w2bits b)) + lzcnt (rev (w2bits b))) = 63 by ring.
qed.

equiv l2 : M.verify_mod_const ~ M.verify_mod_const : ={M.leakages, b} /\ b{1} <> W64.zero ==> ={M.leakages}.
proof.
  proc; inline *; wp; skip => /> &1 &2.
  move: (b{2}) (a{1}) (a{2}) => b a1 a2 {&1 &2} hb.
  rewrite /leak_div_64; congr.
  suff : forall a1,
   leak_div (if 
     (if (LZCNT_64 a1).`5 then W64.one else if (LZCNT_64 b).`5 then W64.zero else W64.of_int 4660) = W64.zero 
   then W64.of_int 18446744073709551615
   else
     if (if (LZCNT_64 a1).`5 then W64.one else if (LZCNT_64 b).`5 then W64.zero else W64.of_int 4660) = W64.one
     then a1
     else
       if LEA_64 ((b `<<` truncateu8 (LZCNT_64 b).`6) + a1) \ult b `<<` truncateu8 (LZCNT_64 b).`6 then
         LEA_64 ((b `<<` truncateu8 ((LZCNT_64 b).`6 - W64.one)) + a1)
       else LEA_64 ((b `<<` truncateu8 (LZCNT_64 b).`6) + a1)) = 0.
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
  rewrite !W64.to_uint_eq /= /LEA_64.
  case: (((b `<<` truncateu8 (LZCNT_64 b).`6) + a1) \ult b `<<` truncateu8 (LZCNT_64 b).`6).
  + move: hzcntb; rewrite /LZCNT_64 /= /ZF_of => hzcntb.
    rewrite /W64.(`<<`) !W8u8.to_uint_truncateu8.
    have hb_bound : 0 <= leak_div b < 64 by smt (leak_div_bound leak_div64).
    have -> : 64 = 2^6 by done.
    rewrite !modz_dvd_pow 1,2:// !W64.to_uint_small 1,2:/# /= !modz_small /= 1,2:/# => /add_le hadd.
    apply leak_div0.
    have heq: to_uint b * 2 ^ (leak_div b - 1) * 2 = to_uint b * 2 ^ leak_div b.
    + have {2}-> : 2 = 2 ^ 1 by done. 
      rewrite mulzA -Ring.IntID.exprD_nneg //; 1: smt(leak_div_bound). 
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
    rewrite /= in hadd => h2; rewrite W64.to_uintD_small /= 1:/#. 
    smt(W64.to_uint_cmp).
  move=> h; apply leak_div0.
  move: h; rewrite W64.shl_shlw. 
  + rewrite /LZCNT_64 /= W64.to_uint_small /= 1: #smt:(leak_div_bound).
    smt (leak_div_bound leak_div64).
  move=> h; rewrite W64.to_uintD_small; 1: by rewrite -add_lt. 
  have := shift_zlcnt b hb.
  smt (W64.to_uint_cmp).
qed.

