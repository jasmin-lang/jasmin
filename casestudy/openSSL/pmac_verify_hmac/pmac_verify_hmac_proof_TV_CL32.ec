from Jasmin require import JModel Leakage_models.
require import AllCore IntDiv CoreMap List Pmac_verify_hmac_ct.

import StdOrder.IntOrder Ring.IntID.

clone import Pmac_verify_hmac_ct.T with theory LeakageModel <-  LeakageModelTVCL32.

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
   if to_sint j < to_sint off then to_uint i = 0
  else if to_sint j < to_sint off + 20 then to_uint i = to_sint j - to_sint off
  else to_uint i = 20.

lemma to_sintD_small (x y : W64.t): 
  W64.min_sint <= to_sint x + to_sint y <= W64.max_sint =>
  to_sint (x + y) = to_sint x + to_sint y.
proof. rewrite /W64.to_sint /smod W64.to_uintD /#. qed.

lemma to_sintB_small (x y : W64.t) : 
  W64.min_sint <= to_sint x - to_sint y <= W64.max_sint =>
  to_sint (x - y) = to_sint x - to_sint y.
proof. rewrite /W64.to_sint /smod W64.to_uintD to_uintNE !modzDmr /= /#. qed.

lemma to_sint_small (x:int) :
  W64.min_sint <= x <= W64.max_sint =>
  to_sint (W64.of_int x) = x.
proof. rewrite /to_sint /smod W64.of_uintK /= /#. qed.

lemma inv_incr (len  maxpad off j i: W64.t):
  to_uint maxpad <= 276 => 
  to_uint len <= to_uint maxpad + 1 =>
  off = (maxpad+ W64.one) - len => 
  W64.to_uint j < to_uint maxpad => 
  inv j off i =>
  inv (j + W64.one) off
    (i + invw (invw (j - off - W64.of_int 20 `|>>` W8.of_int 63)) `&` (off - W64.one - j `|>>` W8.of_int 63) `&` W64.one).
proof.
  rewrite !invwK /W64.(`|>>`) W8.to_uint_small 1:// modz_small 1://.
  rewrite !sar_and /inv => hm hl hoff hj.
  have sulen : to_sint len = to_uint len by rewrite /to_sint /smod /#. 
  have suj : to_sint j = to_uint j by rewrite /to_sint /smod /#. 
  have sumax : to_sint maxpad = to_uint maxpad by rewrite /to_sint /smod /#. 
  have /= ?:= W64.to_uint_cmp j; have /= ?:= W64.to_uint_cmp maxpad; have /= ?:= W64.to_uint_cmp len.
  have h1 := to_sint_small 1 _; 1 : done.
  rewrite (to_sintD_small j W64.one) h1; 1: by rewrite /= /#.
  have hoff' : to_sint off = (to_sint maxpad + 1) - to_sint len.
  + by rewrite hoff to_sintB_small to_sintD_small /to_sint /smod /= // /#.
  have -> : to_sint (j - off - W64.of_int 20) = to_sint j - to_sint off - 20.
  + have -> : j - off - W64.of_int 20 = j - (off + W64.of_int 20) by ring.
    have h : to_sint (off + W64.of_int 20) = to_sint off + 20.
    + by rewrite to_sintD_small ?to_sint_small // hoff to_sintB_small to_sintD_small /= /to_sint /smod /=; smt(). 
    rewrite to_sintB_small h hoff'; 2: by ring.
    by rewrite /to_sint /smod /=; smt().
  have heq : to_sint (off - W64.one - j) = to_sint off - 1 - to_sint j.
  + have -> : off - W64.one - j = off - (W64.one + j) by ring.
    have h : to_sint (W64.one + j) = to_sint j + 1.
    + by rewrite to_sintD_small ?to_sint_small // /= /to_sint /smod /=; smt(). 
    by rewrite to_sintB_small h /= /#.
  case: (to_sint j < to_sint off) => hjoff /=.
  + move=> hi; have -> /= : to_sint j - to_sint off - 20 < 0 by smt().
    by rewrite sar_and heq; have -> /= /#: !(to_sint off - 1 - to_sint j < 0) by smt().
  case: (to_sint j < to_sint off + 20) => hjoff20.
  + have -> /= :  to_sint j - to_sint off - 20 < 0 by smt().
    rewrite sar_and heq => hi.
    have -> /= : !(to_sint j + 1 < to_sint off) by smt().
    have -> /= : to_sint off - 1 - to_sint j < 0 by smt().
    by rewrite W64.to_uintD_small /= /#. 
  have -> /= : !(to_sint j + 1 < to_sint off) by smt().
  have -> /= : !(to_sint j + 1 < to_sint off + 20) by smt().
  have -> // : !(to_sint j - to_sint off - 20 < 0) by smt().
qed.

equiv l_final : M.verify_hmac_jazz ~ M.verify_hmac_jazz :
  ={M.leakages, pmac, maxpad} /\ (out + len){1} = (out + len){2} /\
     to_uint pmac{2} + 32 <= W64.modulus /\ 32 %| to_uint pmac{2} /\ 
     to_uint maxpad{1} < 256  /\
     (to_uint len <= to_uint maxpad + 21){1} /\
     (to_uint len <= to_uint maxpad + 21){2}
     ==> ={M.leakages}.
proof.
proc; wp => /=.
while (={maxpad, j, p, M.leakages, pmac, maxpad} /\ 
       inv j{1} off{1} i{1} /\ inv j{2} off{2} i{2} /\ 
       to_uint j{1} <= to_uint maxpad{1} < 256 + 20 /\ 
       to_uint pmac{2} + 32 <= W64.modulus /\ 32 %| to_uint pmac{2} /\ 
       (off = (maxpad+ W64.one) - len){1} /\ (to_uint len <= to_uint maxpad + 1){1} /\
       (off = (maxpad+ W64.one) - len){2} /\ (to_uint len <= to_uint maxpad + 1){2}).
+ wp; skip=> |> &1 &2 h1 h2 hjm hmax hpmac dpmac hlen1 hlen2; rewrite ultE => hj.
  split; 1: by rewrite /leak_mem /leak_mem_CL32 !offset_div_32 // 1,2:/#.
  split; 1: by apply (inv_incr len{1} maxpad{2}) => // /#. 
  split; 1: by apply (inv_incr len{2} maxpad{2}) => // /#. 
  by rewrite (W64.to_uintD_small j{2} W64.one) /#.
auto => |> &1 &2 houtlen hpmac dmac hmax hlen1 hlen2.
rewrite {1}houtlen /= (W64.to_uintD_small maxpad{2}) /= 1:/# hlen1 hlen2 /=.
have -> : out{1} - (out{1} + len{1} - W64.one - maxpad{2} - W64.of_int 20) = 
          (maxpad{2} + W64.of_int 21) - len{1} by ring.
have -> /= : out{2} - (out{2} + len{2} - W64.one - maxpad{2} - W64.of_int 20) = 
          (maxpad{2} + W64.of_int 21) - len{2} by ring.
have ? : to_sint (maxpad{2} + (of_int 21)%W64) = to_uint maxpad{2} + 21.
+ by rewrite to_sintD_small to_sint_small // /to_sint /smod /=; smt(W64.to_uint_cmp).
split.
+ have ? : to_sint len{1} = to_uint len{1} by rewrite /to_sint /smod /=; smt(W64.to_uint_cmp).
  by rewrite /inv to_sintB_small /= ?to_sint_small //; smt(W64.to_uint_cmp).
split; last by smt(W64.to_uint_cmp).
have ? : to_sint len{2} = to_uint len{2} by rewrite /to_sint /smod /=; smt(W64.to_uint_cmp).
by rewrite /inv to_sintB_small /= ?to_sint_small //; smt(W64.to_uint_cmp).
qed.
