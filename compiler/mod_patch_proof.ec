require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Mod_patch.

(*
lemma lzcnt_zero : forall w, LZCNT_64 (w << LZCNT_64 w) = 0.
*)

lemma lzcnt_size l : 0 <= lzcnt l <= size l.
proof. elim l => //= /#. qed.

(*
lemma lzcnt_split l : lzcnt l = 0 => l = [] \/ exists l', l = true :: l'.
proof. case: l => //; smt (lzcnt_size). qed.
*)

import BitEncoding.BS2Int.

print (^).
search Ring.IntID.(^).

lemma lzcnt_bound l : 
  (if size l = lzcnt (rev l) then 0 else 2^(size l - lzcnt (rev l) - 1))
   <= bs2int l < 2^(size l - lzcnt (rev l)).
proof.
elim /last_ind: l => /=.
+ by rewrite rev_nil /= bs2int_nil.
move=> l b hrec; rewrite rev_rcons /= size_rcons.
rewrite bs2int_rcons; case: b => _ /=; last by smt().
rewrite /b2i /=. 
have -> /= : !(size l + 1 = 0) by smt(size_ge0).
rewrite Ring.IntID.exprD_nneg 1:size_ge0 //=.
smt (bs2int_ge0 bs2int_le2Xs).
qed.

lemma leak_div_bound (w:W64.t) : 0 <= leak_div w <= 64.
proof. smt (lzcnt_size size_mkseq size_rev). qed.

lemma leak_div64 b: b <> W64.zero => leak_div b <> 64.
proof.
  apply contra; rewrite /leak_div => h.
  have := lzcnt_bound (w2bits b).
  rewrite h W64.size_w2bits /= -W64.to_uintE W64.to_uint_eq /= /#.
qed.

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

equiv l2 : M.verify_mod_const ~ M.verify_mod_const : ={M.leakages, b} /\ b{1} <> W64.zero ==> ={M.leakages}.
proof.
  proc; inline *; wp; skip => /> &1 &2.
  move: (b{2}) (a{1}) (a{2}) => b a1 a2 {&1 &2} hb.
  suff : forall a1,
    leak_div
      (if (if (LZCNT_64 a1).`5 then W64.one else if (LZCNT_64 b).`5 then W64.zero else (of_int 4660)%W64) = W64.one 
       then a1
       else
         if LEA_64 ((b `<<` truncateu8 (LZCNT_64 b).`6) + a1) \ult b `<<` truncateu8 (LZCNT_64 b).`6 
         then LEA_64 ((b `<<` truncateu8 ((LZCNT_64 b).`6 - W64.one)) + a1)
         else LEA_64 ((b `<<` truncateu8 (LZCNT_64 b).`6) + a1)) = 0.
   + by move=> h; rewrite !h.
   move=> {a1 a2} a1.
   case: (LZCNT_64 a1).`5 => hzcnta /=.
   + move: hzcnta.
     rewrite /LZCNT_64 /leak_div /ZF_of /= => h.
     have :  W64.to_uint (of_int (lzcnt (rev (w2bits a1))))%W64 =  W64.to_uint W64.zero.
     + by rewrite h.
     rewrite /= W64.to_uint_small //=.
     smt (lzcnt_size W64.size_w2bits size_rev).
   have -> /= : ((if (LZCNT_64 b).`5 then W64.zero else (of_int 4660)%W64) = W64.one) = false.
   + case: (LZCNT_64 b).`5 => hzcntb /=.
     + by rewrite (eq_sym W64.zero) W64.WRingA.oner_neq0.
     by rewrite W64.to_uint_eq.
  rewrite /LEA_64.
  case: (((b `<<` truncateu8 (LZCNT_64 b).`6) + a1) \ult b `<<` truncateu8 (LZCNT_64 b).`6).
  + rewrite /W64.(`<<`).
    admit.
  move=> h; apply leak_div0.
  rewrite W64.shl_shlw. 
  + rewrite /LZCNT_64 /= W64.to_uint_small /= 1:[smt(leak_div_bound)].
    smt (leak_div_bound leak_div64).
  rewrite W64.to_uintD_small.
  + admit.
  rewrite W64.to_uint_shl.
  + admit.
  rewrite modz_small. admit.
  rewrite /LZCNT_64 /= /leak_div.
  have := lzcnt_bound (w2bits b).
  rewrite size_w2bits (eq_sym 64) leak_div64 1:// /= -W64.to_uintE => -[h1 _].
  move: h1.
  rewrite -(StdOrder.IntOrder.ler_pmul2r (2 ^ to_uint (W64.of_int (lzcnt (rev (w2bits b)))))).
  + by rewrite StdOrder.IntOrder.expr_gt0.
  rewrite -StdOrder.IntOrder.Domain.exprD_nneg. 
  + admit.
  + smt (W64.to_uint_cmp).
  rewrite W64.to_uint_small /=. smt ( leak_div_bound ).
  have -> /= : (63 - lzcnt (rev (w2bits b)) + lzcnt (rev (w2bits b))) = 63 by ring.
  smt (W64.to_uint_cmp).
qed.
