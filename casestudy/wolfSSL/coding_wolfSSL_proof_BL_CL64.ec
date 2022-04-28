require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.
require Coding_wolfSSL_ct.
import StdOrder.IntOrder Ring.IntID.

clone import Coding_wolfSSL_ct.T with
theory LeakageModel <-  LeakageModelCL.

lemma offset_div_plus1: forall (p offset : W64.t),
  to_uint p + 128 <= W64.modulus => 64 %| to_uint p => 64 <= to_uint offset < 128 => 
  to_uint (p + offset) %/ 64 = to_uint p %/ 64 + 1.
proof.
move=> /= p offset h1 h2 [] h3 h4. rewrite W64.to_uintD_small /=.
+ smt (W128.to_uint_cmp). by smt().
qed.

lemma and_15_64_zero : (of_int 15)%W8 `&` (of_int 64)%W8 = W8.zero.
proof. by rewrite -(: 2 ^ 4 - 1 = 15) 1:// W8.andwC  and_mod. qed.

lemma l1 (c:W8.t) : 0 <= to_uint (c - W8.of_int 43) && to_uint (c - W8.of_int 43) < 80 => 
  64 <= to_uint (zeroextu64 ((c - W8.of_int 43) `&` W8.of_int 15 `|` W8.of_int 64)) < 128.
proof.
search associative W8.(`&`).
  move=> h; rewrite to_uint_zeroextu64 /= orw_disjoint /=.
  + by rewrite -W8.andwA and_15_64_zero /=.
  rewrite W8.andwC. 
  have /= heq := W8.to_uint_ule_andw (of_int 15)%W8 (c - (of_int 43))%W8.
  rewrite to_uintD_disjoint /=.
  + by rewrite W8.andwC W8.andwA (W8.andwC (W8.of_int _)) and_15_64_zero W8.and0w.
  smt (W8.to_uint_cmp).
qed.

lemma l2 (c:W8.t) : to_uint (zeroextu64 ((c - (of_int 43)%W8) `&` (of_int 63)%W8)) < 64 =>
  to_uint (zeroextu64 ((c - (of_int 43)%W8) `&` (of_int 63)%W8)) < 64.
proof.
  move=> h1; rewrite to_uint_zeroextu64 /=.
  have h := W8.to_uint_ule_andw (c - (of_int 43)%W8) (of_int 63)%W8.
  rewrite -(: 2 ^ 6 - 1 = 63) 1:// to_uint_and_mod // /#. 
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
move=> /> &1 &2 h1 h2 h3 h4 h5 h6; split.
+ by rewrite /leak_mem /= /leak_mem_CL /= !offset_div_plus1 //; apply l1.
rewrite /leak_mem /= /leak_mem_CL /= !offset_div //; 1,3: by smt().
+ rewrite to_uint_zeroextu64 /= -(: 2 ^ 6 - 1 = 63) 1:// to_uint_and_mod // /#.  
rewrite to_uint_zeroextu64 /= -(: 2 ^ 6 - 1 = 63) 1:// to_uint_and_mod // /#.  
qed.
