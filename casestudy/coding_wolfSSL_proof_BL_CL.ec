require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Coding_wolfSSL.
import StdOrder.IntOrder Ring.IntID.

clone import Coding_wolfSSL.T with
theory LeakageModel <-  LeakageModelCL.

lemma offset_div_plus1:
  forall (p offset : W64.t),
    to_uint p + 64 <= W64.modulus =>
    64 %| to_uint p =>
    64 <= to_uint offset < 128 => to_uint (p + offset) %/ 64 = to_uint p %/ 64 + 1.
admitted.

    
(* input base64decode is public and (base64decode % 64 == 0) 
   input c is secret *)
equiv l_final : M.base64_Char2Val_jazz ~ M.base64_Char2Val_jazz :
={M.leakages} /\ (base64Decode{1} = base64Decode{2}) /\
(to_uint base64Decode{1} + 64 <= W64.modulus) /\
(64 %| W64.to_uint base64Decode{1}) /\
(0 <= to_uint (c{1} - (of_int 43)%W8) < 80) /\
(0 <= to_uint (c{2} - (of_int 43)%W8) < 80)
==> ={M.leakages}.
proof.
proc; inline *; auto.
move=> &1 &2 [] hleak [] hp [] h1 [] h2 [] h3 h4 /=. split=> //=.
+ rewrite hp. 
  rewrite /leak_mem /= /leak_mem_CL /=. rewrite offset_div_plus1. 
+ by rewrite -hp. 
+ by rewrite -hp.
+ admit.
admit.
rewrite hp /=. rewrite /leak_mem /= /leak_mem_CL /=.
split=> //=. rewrite !offset_div. 
+ by rewrite -hp. 
+ by rewrite -hp.
+ case: h3=> h3 h3'. rewrite to_uint_zeroextu64 /=.
  have h := W8.to_uint_ule_andw (c{1} - (of_int 43)%W8) (of_int 63)%W8.
  have heq : 2 ^ 6 - 1 = 63. + by auto. rewrite -heq.
  rewrite to_uint_and_mod. + by auto. by smt.
+ by rewrite -hp. 
+ by rewrite -hp.
+ case: h3=> h3 h3'. rewrite to_uint_zeroextu64 /=.
  have h := W8.to_uint_ule_andw (c{1} - (of_int 43)%W8) (of_int 63)%W8.
  have heq : 2 ^ 6 - 1 = 63. + by auto. rewrite -heq.
  rewrite to_uint_and_mod. + by auto. by smt.
by auto.
admitted.
