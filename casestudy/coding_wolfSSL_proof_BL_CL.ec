require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Coding_wolfSSL.
import StdOrder.IntOrder Ring.IntID.

clone import Coding_wolfSSL.T with
theory LeakageModel <-  LeakageModelCL.

(* input base64decode is public and (base64decode % 64 == 0) 
   input c is secret *)
  (* need to take the pre condition as sub-lemmas *)
equiv l_final : M.base64_Char2Val_jazz ~ M.base64_Char2Val_jazz :
={M.leakages} /\ (base64Decode{1} = base64Decode{2}) /\
(0 <= to_uint (c{1} - (of_int 43)%W8) < 80) /\
(0 <= to_uint (c{2} - (of_int 43)%W8) < 80)
==> ={M.leakages}.
proof.
proc; inline *; auto; rewrite /=.
move=> &1 &2 [] hleak [] hp [] h1 h2 /=. split=> //=.
+ rewrite hp. case: h1=> h1 h1'. case: h2=> h2 h2'.
  rewrite /leak_mem /= /leak_mem_CL /=. rewrite !offset_div.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  by auto.
rewrite hp /=. rewrite /leak_mem /= /leak_mem_CL /=.
split=> //=. rewrite !offset_div.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
by auto.
admitted.
