require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array128 WArray128.

require Copy_mac_ct.

op leak_div (a: W32.t) : int =
  lzcnt (rev (w2bits a)).

theory LeakageModelDiv.

op leak_div_32 (a b: W32.t) : address list =
[ leak_div a ; to_uint b ].

op leak_div_64 (a b: W64.t) : address list =
[ to_uint a ; to_uint b ].

op leak_mem (a: address) : address = a.

end LeakageModelDiv.

clone import Copy_mac_ct.T with
theory LeakageModel <- LeakageModelDiv.

equiv l_constant_time_lt_jasmin : M.constant_time_lt_jasmin ~ M.constant_time_lt_jasmin :
={M.leakages}
==> ={M.leakages}.
proof.
proc; inline *; sim.
qed.

lemma leak_div_or (x y : W32.t) : leak_div (x `|` y) = min (leak_div x) (leak_div y).
proof.
  rewrite /leak_div /w2bits.
  elim/natind: 32.
  + by move=> n hn; rewrite !mkseq0_le 1..3:// /= rev_nil.
  move=> n hn hrec; rewrite !mkseqS 1..3:// !rev_rcons /= hrec; smt(lzcnt_size).
qed.

import BitEncoding.BS2Int.

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

lemma leak_div_bound (w:W32.t) : 0 <= leak_div w <= 32.
proof. smt (lzcnt_size size_mkseq size_rev). qed.

lemma nosmt ltr_weexpn2l x m n:
   2 <= x => 0 <= m => 0 <= n => 
   m < n <=> x ^ m < x ^ n.
proof.
  move=> h1 h2 h3; case: (m < n) => /= h4. 
  + have -> : n = (n - m) + m by ring.
    rewrite Ring.IntID.exprD_nneg 1:/# 1://.
    rewrite -{1}(Ring.IntID.div1r (x^m)).
    rewrite StdOrder.IntOrder.ltr_pmul2r.
    + smt (StdOrder.IntOrder.expr_gt0).
    smt (StdOrder.IntOrder.exprn_egt1).
  have -> : m = (m - n) + n by ring.
  rewrite Ring.IntID.exprD_nneg 1:/# 1:// -lezNgt.  
  rewrite -{1}(Ring.IntID.div1r (x^n)).
  rewrite StdOrder.IntOrder.ler_pmul2r.
  + smt (StdOrder.IntOrder.expr_gt0).
  smt (StdOrder.IntOrder.exprn_ege1).
qed.

lemma leak_div_le (w1 w2: W32.t) : to_uint w1 <= to_uint w2 => leak_div w2 <= leak_div w1.
proof.
  rewrite W32.to_uintE /leak_div.
  have := lzcnt_bound (w2bits w1).
  have := lzcnt_bound (w2bits w2).
  rewrite !size_w2bits => h1 h2 h3.
  have : (if 32 = lzcnt (rev (w2bits w1)) then 0 else 2 ^ (32 - lzcnt (rev (w2bits w1)) - 1)) <
         2 ^ (32 - lzcnt (rev (w2bits w2))) by smt().
  case (32 = lzcnt (rev (w2bits w1))) => /= [ <- | ] h; 1: smt (leak_div_bound).
  rewrite -ltr_weexpn2l 1://; smt(leak_div_bound).
qed.

(* Remark: the shift by 23 look arbitrary. I think a shift by 8 is suffisant *)
lemma l_rotate_offset_div_core (x md_size : W32.t) :    
  0 <= to_uint x < 2^8 => 
  16 <= to_uint md_size <= 64 => 
  leak_div (x + (md_size `<<` W8.of_int 23)) = leak_div (md_size `<<` W8.of_int 23).
proof.
  move=> /= h1 h2.
  pose md23 := md_size `<<` W8.of_int 23.
  rewrite -(W32.orw_disjoint _ md23).
  + apply W32.wordP => i hi; rewrite W32.zerowE W32.andwE.
    rewrite !W32.get_to_uint hi /=.
    case: (i < 8) => hi'.
    + rewrite /md23 /(`<<`) /= W32.to_uint_shl 1:// IntDiv.modz_pow2_div.
      + by apply StdOrder.IntOrder.divr_ge0; 1: smt(W32.to_uint_cmp).
      + smt().
      have h21 : 2 = 2 ^ 1 by done.
      rewrite {6}h21 modz_dvd_pow 1:/#.
      have -> : 2 ^ 23 = 2 ^ (23 - i - 1) * 2 * 2 ^ i.
      + by rewrite {3}h21 -!Ring.IntID.exprD_nneg 1,3,4:/# 1://; congr; ring.
      rewrite -(mulzA (W32.to_uint _)) mulzK; 1: smt(gt0_pow2).
      by rewrite -mulzA modzMl.
    rewrite divz_small //.
    by have /= /# :=StdOrder.IntOrder.ler_weexpn2l 2 _ 8 i.
  rewrite leak_div_or.
  have : leak_div (W32.of_int 256) <= leak_div x.
  + by apply leak_div_le => /= /#.
  have -> : leak_div (W32.of_int 256) = 23.
  + by rewrite /leak_div /w2bits /mkseq -iotaredE /= !W32.of_intwE; cbv delta.
  have : leak_div md23 <= leak_div (W32.of_int (2^23)).
  + by apply leak_div_le; rewrite /md23 /(`<<`) /= !W32.to_uint_shl //= modz_small /#.
  have -> /# : leak_div (W32.of_int (2^23)) = 8.
  by rewrite /leak_div /w2bits /mkseq -iotaredE /= !W32.of_intwE; cbv delta.
qed.

(* Remark: the shift by 23 look arbitrary. I think a shift by 8 is suffisant *)
equiv l_rotate_offset_div : M.rotate_offset_div ~ M.rotate_offset_div:
={M.leakages, md_size, scan_start} /\
(0 <= (to_uint (mac_start - scan_start)) < 2^8){1} /\ 
(0 <= (to_uint (mac_start - scan_start)) < 2^8){2} /\
 (16 <= to_uint md_size <= 64){1} 
==> ={M.leakages}.
proof. by proc; wp; skip => /> &1 &2 *; rewrite /leak_div_32 !l_rotate_offset_div_core. qed.

op wf_rec mem (rec:W64.t) (orig_len md_size : W32.t) = 
 let mac_end = loadW32 mem (to_uint (rec + W64.of_int 4)) in
 to_uint md_size <= to_uint mac_end /\ 
 1 <= to_uint orig_len - to_uint mac_end <= 256.

lemma wf_rec_cond_md_size_mac_end mem rec orig_len md_size : 
  16 <= W32.to_uint md_size <= 64 =>
  wf_rec mem rec orig_len md_size =>
  let mac_end = loadW32 mem (to_uint (rec + W64.of_int 4)) in
  if (md_size + W32.of_int 256 \ult orig_len) then 
     0 <= to_uint (mac_end - md_size - (orig_len - (md_size + W32.of_int 256))) < 256
  else 0 <= to_uint (mac_end - md_size - W32.zero) < 256.
proof.
  rewrite /wf_rec /=.
  pose mac_end := loadW32 _ _; move: mac_end => mac_end hmd [h1 [h2 h3]].
  have -> : mac_end - md_size - (orig_len - (md_size + W32.of_int 256)) = 
            mac_end - (orig_len - W32.of_int 256) by ring.
  rewrite W32.ultE W32.to_uintD_small /= 1:/#.
  case: (to_uint md_size + 256 < to_uint orig_len) => h; last first.
  + rewrite W32.WRingA.subr0 W32.to_uintB 1:W32.uleE 1:// /#.
  rewrite W32.to_uintB ?W32.uleE W32.to_uintB ?W32.uleE /=; smt(W32.to_uint_cmp). 
qed.

equiv l_rotate_mac_ct : M.rotate_mac ~ M.rotate_mac : ={M.leakages, out, md_size} ==> ={M.leakages}.
proof. by proc; inline *; sim. qed.

equiv l_final : M.ssl3_cbc_copy_mac_jasmin ~ M.ssl3_cbc_copy_mac_jasmin :
={M.leakages, md_size, orig_len, out, rec} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = 
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2} /\
16 <= to_uint md_size{2} <= 64 /\
(wf_rec Glob.mem rec orig_len md_size){1} /\ 
(wf_rec Glob.mem rec orig_len md_size){2}  
==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_ct; wp.
  call l_constant_time_lt_jasmin; wp.
  while (={M.leakages, temp, out, md_size}); 1: by sim.
  wp => /=; conseq />.
  call l_rotate_offset_div; wp.
  while (={i, j, orig_len, data, md_size, M.leakages}); 1: by inline*;sim.
  wp => /=; while (={i, md_size, M.leakages}); 1: by sim.
  wp; skip => |> &1 &2; smt (wf_rec_cond_md_size_mac_end).
qed.
