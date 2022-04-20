require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Coding_wolfSSL.
import StdOrder.IntOrder Ring.IntID.

clone import Coding_wolfSSL.T with
theory LeakageModel <-  LeakageModelCL.

lemma offset_div_plus1: forall (p offset : W64.t),
to_uint p + 128 <= W64.modulus =>
64 %| to_uint p =>
64 <= to_uint offset < 128 => to_uint (p + offset) %/ 64 = to_uint p %/ 64 + 1.
proof.
move=> /= p offset h1 h2 [] h3 h4. rewrite W64.to_uintD_small /=. 
+ smt (W128.to_uint_cmp). by smt.
qed.

lemma bitand_assoc a b c: a `&` (b `&` c)%W8 = a `&` b `&` c.
proof. smt. qed.

lemma bitand_assoc' a b c: ((a `&` b) `&` c)%W8 = a `&` b `&` c.
proof. smt. qed.

lemma bitand_reflex a b: (a `&` b)%W8 = (b `&` a)%W8.
proof. smt. qed.

lemma and_15_64_zero : (of_int 15)%W8 `&` (of_int 64)%W8 = W8.zero.
proof.
rewrite bitand_reflex. have heq : 2 ^ 4 - 1 = 15. + by auto. rewrite -heq. print and_mod.   
rewrite and_mod /=;by auto. 
qed.
  
(* input base64decode is public and (base64decode % 64 == 0) 
   input c is secret *)
equiv l_final : M.base64_Char2Val_jazz ~ M.base64_Char2Val_jazz :
={M.leakages} /\ (base64Decode{1} = base64Decode{2}) /\
(to_uint base64Decode{1} + 128 <= W64.modulus) /\
(64 %| W64.to_uint base64Decode{1}) /\
(0 <= to_uint (c{1} - (of_int 43)%W8) < 80) /\
(0 <= to_uint (c{2} - (of_int 43)%W8) < 80)
==> ={M.leakages}.
proof.
proc; inline *; auto.
move=> &1 &2 [] hleak [] hp [] h1 [] h2 [] h3 h4 /=. split=> //=.
+ rewrite hp /leak_mem /= /leak_mem_CL /= !offset_div_plus1. 
  + by rewrite -hp. 
  + by rewrite -hp.
  + split=> //=.
    + rewrite to_uint_zeroextu64 /= orw_disjoint /=.
      + by rewrite -bitand_assoc and_15_64_zero /=.
      rewrite bitand_reflex.
      have /= heq := W8.to_uint_ule_andw (of_int 15)%W8 (c{1} - (of_int 43))%W8.
      rewrite to_uintD_disjoint /=.
      + have hand := and_15_64_zero. rewrite bitand_reflex in hand.
        rewrite bitand_reflex bitand_assoc bitand_reflex hand. by smt.
      by smt.
    move=> h. rewrite to_uint_zeroextu64 /= in h. rewrite to_uint_zeroextu64 /= orw_disjoint /=.
    + by rewrite -bitand_assoc and_15_64_zero /=. 
    rewrite bitand_reflex.
    have /= heq := W8.to_uint_ule_andw (of_int 15)%W8 (c{1} - (of_int 43))%W8.
    rewrite to_uintD_disjoint /=.
    + have hand := and_15_64_zero. rewrite bitand_reflex in hand.
      rewrite bitand_reflex bitand_assoc bitand_reflex hand. by smt.
    by smt.
  + by rewrite -hp.
  + by rewrite -hp.
  + split=> //=.
    + rewrite to_uint_zeroextu64 /= orw_disjoint /=.
      + by rewrite -bitand_assoc and_15_64_zero /=.
      rewrite bitand_reflex.
      have /= heq := W8.to_uint_ule_andw (of_int 15)%W8 (c{2} - (of_int 43))%W8.
      rewrite to_uintD_disjoint /=.
      + have hand := and_15_64_zero. rewrite bitand_reflex in hand.
        rewrite bitand_reflex bitand_assoc bitand_reflex hand. by smt.
      by smt.
    move=> h. rewrite to_uint_zeroextu64 /= in h. rewrite to_uint_zeroextu64 /= orw_disjoint /=.
    + by rewrite -bitand_assoc and_15_64_zero /=.
    rewrite bitand_reflex.
    have /= heq := W8.to_uint_ule_andw (of_int 15)%W8 (c{2} - (of_int 43))%W8.
    rewrite to_uintD_disjoint /=.
    + have hand := and_15_64_zero. rewrite bitand_reflex in hand.
      rewrite bitand_reflex bitand_assoc bitand_reflex hand. by smt.
    by smt.
  + by auto.
rewrite hp /= /leak_mem /= /leak_mem_CL /=.
split=> //=. rewrite !offset_div. 
+ by smt. 
+ by smt.
+ rewrite to_uint_zeroextu64 /=.
  have h := W8.to_uint_ule_andw (c{1} - (of_int 43)%W8) (of_int 63)%W8.
  have heq : 2 ^ 6 - 1 = 63. + by auto.
  rewrite -heq to_uint_and_mod. + by auto. by smt.
+ by smt. 
+ by smt.
+ rewrite to_uint_zeroextu64 /=.
  have h := W8.to_uint_ule_andw (c{1} - (of_int 43)%W8) (of_int 63)%W8.
  have heq : 2 ^ 6 - 1 = 63. + by auto. 
  rewrite -heq to_uint_and_mod. + by auto. by smt.
by auto.
qed.
