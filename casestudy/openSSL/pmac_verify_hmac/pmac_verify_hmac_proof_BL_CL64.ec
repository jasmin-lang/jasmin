require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.
require Pmac_verify_hmac_ct.
import StdOrder.IntOrder Ring.IntID.

clone import Pmac_verify_hmac_ct.T with
theory LeakageModel <-  LeakageModelCL.

equiv l_final : M.verify_hmac_jazz ~ M.verify_hmac_jazz :
={M.leakages, len, pmac, out, maxpad} /\
  to_uint pmac{2} + 64 <= W64.modulus /\
  64 %| to_uint pmac{2}
==> ={M.leakages}.
proof.
proc; inline *; auto.
while (={maxpad, j, p, M.leakages, len, pmac, out, maxpad} /\ to_uint pmac{2} + 64 <= W64.modulus
        /\ 64 %| to_uint pmac{2} /\ 0 <= to_uint i{1} < 20 /\ 0 <= to_uint i{2} < 20).
wp; skip=> />.
+ move=> &1 &2 /= hpmac hdiv64 h0i hi20 h0i' hi20' ht.
  rewrite /leak_mem /= /leak_mem_CL /=. split=> //=. rewrite !offset_div.
  + by apply hpmac.
  + by apply hdiv64.
  + by smt().
  + by apply hpmac.
  + by apply hdiv64.
  + by smt().
  + by auto.
  split=> //=; auto. split=> //=; auto.
  + have hle := W64.to_uint_ule_andw ((i{1} + W64.one)%W64)
    (zeroextu64
    (invw (invw (truncateu32 j{2} - truncateu32 off{1} - (of_int 20)%W32 `>>`(of_int 31)%W8)))).
    have hadd : 1 <= to_uint (i{1} + W64.one) < 21.
    + split=> //=.
      + rewrite to_uintD_small. + by smt().
      rewrite /=. by smt().
    move=> hadd'. + rewrite to_uintD_small. + by smt().
    rewrite /=. by smt().
    case: hadd=> hadd1 hadd2. by smt.
  + move=> h.
    have hle := W64.to_uint_ule_andw ((i{1} + W64.one)%W64)
    (zeroextu64
    (invw (invw (truncateu32 j{2} - truncateu32 off{1} - (of_int 20)%W32 `>>`(of_int 31)%W8)))).
    have hadd : 1 <= to_uint (i{1} + W64.one) < 21.
    + split=> //=.
      + rewrite to_uintD_small. + by smt().
      rewrite /=. by smt().
    move=> hadd'. + rewrite to_uintD_small. + by smt().
    rewrite /=. by smt().
    admit.
  + split=> //=; auto.
    + have hle := W64.to_uint_ule_andw ((i{2} + W64.one)%W64)
    (zeroextu64
    (invw (invw (truncateu32 j{2} - truncateu32 off{2} - (of_int 20)%W32 `>>`(of_int 31)%W8)))).
    have hadd : 1 <= to_uint (i{2} + W64.one) < 21.
    + split=> //=.
      + rewrite to_uintD_small. + by smt().
      rewrite /=. by smt().
    move=> hadd'. + rewrite to_uintD_small. + by smt().
    rewrite /=. by smt().
    case: hadd=> hadd1 hadd2. by smt.
  + move=> h.
    have hle := W64.to_uint_ule_andw ((i{2} + W64.one)%W64)
    (zeroextu64
    (invw (invw (truncateu32 j{2} - truncateu32 off{2} - (of_int 20)%W32 `>>`(of_int 31)%W8)))).
    have hadd : 1 <= to_uint (i{2} + W64.one) < 21.
    + split=> //=.
      + rewrite to_uintD_small. + by smt().
      rewrite /=. by smt().
    move=> hadd'. + rewrite to_uintD_small. + by smt().
    rewrite /=. by smt(). admit.
wp; skip=> />.
admitted.
