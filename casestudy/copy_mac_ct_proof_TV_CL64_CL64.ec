from Jasmin require import JModel Leakage_models.
require import AllCore IntDiv CoreMap List Array64 WArray64 Copy_mac_ct.

clone import Copy_mac_ct.T with theory LeakageModel <- LeakageModelCL.

equiv l_rotate_offset_TVCL md_size_ : M.rotate_offset_TV ~ M.rotate_offset_TV:
  ={M.leakages, md_size, scan_start} /\ md_size{1} = md_size_ /\
  (16 <= to_uint md_size <= 64){1}
  ==>
  ={M.leakages} /\ to_uint res{1} < to_uint md_size_ /\ to_uint res{2} < to_uint md_size_.
proof.
  proc; wp; skip => />; smt (W32.to_uint_small W32.to_uint_cmp).
qed.

equiv l_rotate_mac_CL : M.rotate_mac_CL ~ M.rotate_mac_CL :
  ={M.leakages, out, md_size, rotated_mac} /\ 64 %| W64.to_uint rotated_mac{1} /\
  to_uint rotated_mac{1} + 64 <= W64.modulus /\ (* This hypothesis is implied by  64 %| W64.to_uint rotated_mac{1} we should remove it *)
  16 <= to_uint md_size{1} <= 64 /\
  to_uint rotate_offset{1} < to_uint md_size{1}  /\ to_uint rotate_offset{2} < to_uint md_size{1}
  ==>
  ={M.leakages}.
proof.
  proc.
  while (={out, rotated_mac, md_size, i, M.leakages, zero} /\ 64 %| W64.to_uint rotated_mac{1} /\
         to_uint rotated_mac{1} + 64 <= W64.modulus /\
         16 <= to_uint md_size{1} <= 64 /\
         zero{1} = W64.zero /\
         to_uint ro{1} < to_uint md_size{1}  /\ to_uint ro{2} < to_uint md_size{1});
  wp; skip => />; last by rewrite !to_uint_zeroextu64.
  move => &1 &2 hmod nover h1 h2 h3 h4 hi.
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

equiv l_init_rotated_mac_mem :
  M.init_rotated_mac_mem ~ M.init_rotated_mac_mem :
  ={md_size, rotated_mac, data, orig_len, scan_start, M.leakages} ==> ={M.leakages}.
proof. by proc; sim. qed.

equiv l_final : M.ssl3_cbc_copy_mac_TV_CL ~ M.ssl3_cbc_copy_mac_TV_CL :
  ={M.leakages, md_size, orig_len, out, rec, rotated_mac} /\
  (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2} /\
  to_uint rotated_mac{2} + 64 <= W64.modulus /\ 64 %| to_uint rotated_mac{2} /\
  16 <= to_uint md_size{2} <= 64
  ==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_CL; wp.
  ecall (l_rotate_offset_TVCL md_size{1}); wp.
  call l_init_rotated_mac_mem.
  by inline *; auto.
qed.
