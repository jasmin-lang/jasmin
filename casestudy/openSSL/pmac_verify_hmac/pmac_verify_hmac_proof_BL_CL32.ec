from Jasmin require import JModel Leakage_models.
require import AllCore IntDiv CoreMap List Pmac_verify_hmac_ct.

import StdOrder.IntOrder Ring.IntID.

clone import Pmac_verify_hmac_ct.T with theory LeakageModel <-  LeakageModelCL32.

lemma invwK (c:W64.t) : invw (invw c) = c.
proof. by apply W64.wordP => i hi; rewrite !W64.invwE hi. qed.

lemma sar_and (x y:W64.t): W64.sar x 63 `&` y = if to_sint x < 0 then y else W64.zero.
proof.
  apply W64.wordP => i hi.
  rewrite W64.andwE /sar W64.initiE 1:// /=.
  have -> : min 63 (i + 63) = 63 by smt().
  rewrite to_sintE /smod W64.get_to_uint /=.
  have /= := W64.to_uint_cmp x; smt (W64.zerowE).
qed.

op inv (j off i:W64.t) = 
   if to_uint j < to_uint off then to_uint i = 0
  else if to_uint j < to_uint off + 20 then to_uint i = to_uint j - to_uint off
  else to_uint i = 20.

lemma inv_incr j off i : 
  W64.to_uint j < 276 => 
  inv j off i =>
  inv (j + W64.one) off
    (i + invw (invw (j - off - W64.of_int 20 `|>>` W8.of_int 63)) `&` (off - W64.one - j `|>>` W8.of_int 63) `&` W64.one).
proof.
  rewrite !invwK /W64.(`|>>`) W8.to_uint_small 1:// modz_small 1://.
  rewrite !sar_and /inv => /> hj.
  rewrite (W64.to_uintD_small j W64.one) 1:/#.
  have -> : to_sint (j - off - W64.of_int 20) = to_uint j - to_uint off - 20.
  + admit.
  have heq : to_sint (off - W64.one - j) = to_uint off - 1 - to_uint j.
  + admit.
  case: (to_uint j < to_uint off) => hjoff /=.
  + move=> hi; have -> /= : to_uint j - to_uint off - 20 < 0 by smt().
    by rewrite sar_and heq; have -> /= /#: !(to_uint off - 1 - to_uint j < 0) by smt().
  case: (to_uint j < to_uint off + 20) => hjoff20.
  + have -> /= :  to_uint j - to_uint off - 20 < 0 by smt().
    rewrite sar_and heq => hi.
    split => hj1.
    + by have -> /= : !(to_uint off - 1 - to_uint j < 0); smt().
    case: (to_uint off - 1 - to_uint j < 0) => hoff1j /=.
    + by rewrite (W64.to_uintD_small i W64.one) /= /#.
    smt().    
  have -> /= : !(to_uint j - to_uint off - 20 < 0); smt().
qed.

equiv l_final : M.verify_hmac_jazz ~ M.verify_hmac_jazz :
  ={M.leakages, len, pmac, out, maxpad} /\ to_uint pmac{2} + 32 <= W64.modulus /\ 32 %| to_uint pmac{2} /\ to_uint maxpad{1} < 256 
  ==> ={M.leakages}.
proof.
proc; wp => /=.
while (={maxpad, j, p, M.leakages, len, pmac, out, maxpad} /\ 
       inv j{1} off{1} i{1} /\ inv j{2} off{2} i{2} /\ to_uint j{1} <= to_uint maxpad{1} < 256 + 20 /\ 
       to_uint pmac{2} + 32 <= W64.modulus /\ 32 %| to_uint pmac{2}).
+ wp; skip=> |> &1 &2 h1 h2 hjm hmax hpmac dpmac; rewrite ultE => hj.
  split.
  + by rewrite /leak_mem /leak_mem_CL32 !offset_div_32 // 1,2:/#.
  split; 1: by apply inv_incr => //; smt().
  split; 1: by apply inv_incr => //; smt().
  by rewrite (W64.to_uintD_small j{2} W64.one) /#.
auto => |> &2 hmac dmac hmax.
rewrite (W64.to_uintD_small maxpad{2}) /= 1:/#.
have -> : out{2} - (out{2} + len{2} - W64.one - maxpad{2} - W64.of_int 20) = 
          (W64.one + maxpad{2} + W64.of_int 20) - len{2} by ring.
rewrite /inv /=; smt(W64.to_uint_cmp).
qed.
