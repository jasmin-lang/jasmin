require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Pmac_verify_hmac.
import StdOrder.IntOrder Ring.IntID.

clone import Pmac_verify_hmac.T with
theory LeakageModel <-  LeakageModelCL32.

lemma offset_div_32 (p offset : W64.t) :
  to_uint p + 32 <= W64.modulus =>
  32 %| to_uint p =>
  0 <= to_uint offset < 32 =>
  to_uint (p + offset) %/ 32  = to_uint p %/ 32.
proof. move=> /= h1 h2 h3; rewrite W64.to_uintD_small /= 1:/# divzDl 1:// /#. qed.

equiv l_final : M.verify_hmac_jazz ~ M.verify_hmac_jazz :
={M.leakages, len, pmac, out, maxpad} /\
  to_uint pmac{2} + 32 <= W64.modulus /\
  32 %| to_uint pmac{2}
==> ={M.leakages}.
proof.
proc; inline *; auto.
while (={maxpad, j, p, M.leakages, len, pmac, out, maxpad} /\ to_uint pmac{2} + 32 <= W64.modulus
        /\ 32 %| to_uint pmac{2}).
wp; skip=> />.
+ move=> &1 &2 /= hpmac hdiv32 ht. 
  rewrite /leak_mem /= /leak_mem_CL32 /=. rewrite !offset_div_32.
  + by apply hpmac.
  + by apply hdiv32.
  + have hi : 0 <= to_uint i{1} < 20. + admit. by smt.
  + by apply hpmac.
  + by apply hdiv32.
  + have hi : 0 <= to_uint i{2} < 20. + admit. by smt.
  by auto.
wp; skip=> />.
qed.
