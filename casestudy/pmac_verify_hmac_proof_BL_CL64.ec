require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Pmac_verify_hmac.
import StdOrder.IntOrder Ring.IntID.

clone import Pmac_verify_hmac.T with
theory LeakageModel <-  LeakageModelCL.

equiv l_final : M.verify_hmac_jazz ~ M.verify_hmac_jazz :
={M.leakages, len, pmac, out, maxpad} /\
  to_uint pmac{2} + 64 <= W64.modulus /\
  64 %| to_uint pmac{2}
==> ={M.leakages}.
proof.
proc; inline *; auto.
while (={maxpad, j, p, M.leakages, len, pmac, out, maxpad} /\ to_uint pmac{2} + 64 <= W64.modulus
        /\ 64 %| to_uint pmac{2}).
wp; skip=> />.
+ move=> &1 &2 /= hpmac hdiv64 ht. 
  rewrite /leak_mem /= /leak_mem_CL /=. rewrite !offset_div.
  + by apply hpmac.
  + by apply hdiv64.
  + have hi : 0 <= to_uint i{1} < 20. + admit. by smt.
  + by apply hpmac.
  + by apply hdiv64.
  + have hi : 0 <= to_uint i{2} < 20. + admit. by smt.
  by auto.
wp; skip=> />.
qed.
