require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array128 WArray128.

require Copy_mac_ct.
require import Leakage_models.

clone import Copy_mac_ct.T with
theory LeakageModel <- LeakageModelCL.

equiv l_rotate_offset_BLCL md_size_ : M.rotate_offset_BL ~ M.rotate_offset_BL:
={M.leakages, md_size, scan_start} /\ md_size{1} = md_size_ /\
(16 <= to_uint md_size <= 64){1}
==> ={M.leakages} /\ 0 <= to_uint res{1} < to_uint md_size_ /\ 0 <= to_uint res{2} < to_uint md_size_.
proof.
  proc; wp; skip => /> *.
  rewrite /leak_div_32;
  smt (W32.to_uint_small W32.to_uint_cmp).
qed.

lemma offset_div (p offset : W64.t) :
  to_uint p + 64 <= W64.modulus =>
  64 %| to_uint p =>
  0 <= to_uint offset < 64 =>
  to_uint (p + offset) %/ 64  = to_uint p %/ 64.
proof.
  move=> /= h1 h2 h3; rewrite W64.to_uintD_small /= 1:/# divzDl 1:// /#.
qed.

lemma to_uint_truncateu32_small (x: W64.t) :
    to_uint x < W32.modulus =>
    to_uint (truncateu32 x) = to_uint x.
proof.
  move => h; rewrite to_uint_truncateu32 modz_small => />.
  smt (W64.to_uint_cmp).
qed.

equiv l_rotate_mac_CL : M.rotate_mac_CL ~ M.rotate_mac_CL :
  ={M.leakages, out, md_size, rotated_mac} /\ 64 %| W64.to_uint rotated_mac{1} /\
  to_uint rotated_mac{1} + 64 <= W64.modulus /\ (* This hypothesis is implied by  64 %| W64.to_uint rotated_mac{1} we should remove it *)
  16 <= to_uint md_size{1} <= 64 /\
  0 <= to_uint rotate_offset{1} < to_uint md_size{1}  /\ 0 <= to_uint rotate_offset{2} < to_uint md_size{1}
  ==>
  ={M.leakages}.
proof.
  proc.
  while (={out, rotated_mac, md_size, i, M.leakages, zero} /\ 64 %| W64.to_uint rotated_mac{1} /\
         to_uint rotated_mac{1} + 64 <= W64.modulus /\
         16 <= to_uint md_size{1} <= 64 /\
         zero{1} = W64.zero /\
         0 <= to_uint ro{1} < to_uint md_size{1}  /\ 0 <= to_uint ro{2} < to_uint md_size{1});
  wp; skip => />; last by rewrite !to_uint_zeroextu64.
  move => &1 &2 hmod nover h1 h2 h3 h4 h5 h6 hi.
  rewrite /leak_mem /leak_mem_CL !offset_div //= 1, 2: /#.
  have heq1 : to_uint (ro{1} + W64.one) = to_uint ro{1} + 1 by rewrite W64.to_uintD_small //= /#.
  have hlt1 : to_uint (ro{1} + W64.one) < W32.modulus by rewrite heq1 /= /#.
  have heq2 : to_uint (ro{2} + W64.one) = to_uint ro{2} + 1 by rewrite W64.to_uintD_small //= /#.
  have hlt2 : to_uint (ro{2} + W64.one) < W32.modulus by rewrite heq2 /= /#.
  case: (md_size{2} \ule truncateu32 (ro{1} + W64.one)); 
  rewrite uleE to_uint_truncateu32_small // heq1 /=;
  case: (md_size{2} \ule truncateu32 (ro{2} + W64.one)); 
  rewrite uleE to_uint_truncateu32_small // heq2 /= /#.
qed.

equiv l_final : M.ssl3_cbc_copy_mac_BL_CL ~ M.ssl3_cbc_copy_mac_BL_CL :
={M.leakages, md_size, orig_len, out, rec, rotated_mac} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2} /\
to_uint rotated_mac{2} + 64 <= W64.modulus /\ 64 %| to_uint rotated_mac{2} /\
16 <= to_uint md_size{2} <= 64
==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_CL; wp.
  ecall (l_rotate_offset_BLCL md_size{1}); wp.
  while (={i, j, orig_len, data, rotated_mac, md_size, zero, M.leakages}); 1: by sim.
  wp; skip => |> &1 &2.
qed.
