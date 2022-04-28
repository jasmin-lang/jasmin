require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.

require import Array64 WArray64.

require Copy_mac_ct.

clone import Copy_mac_ct.T with
theory LeakageModel <- LeakageModelBL.

equiv l_rotate_offset_TV : M.rotate_offset_TV ~ M.rotate_offset_TV : ={M.leakages, md_size, scan_start} ==> ={M.leakages}.
proof. by proc; auto. qed.

equiv l_rotate_mac_BL : M.rotate_mac_BL ~ M.rotate_mac_BL : ={M.leakages, out, md_size} ==> ={M.leakages}.
proof. by proc; inline *; sim. qed.

equiv l_init_rotated_mac_stk : M.init_rotated_mac_stk ~ M.init_rotated_mac_stk :
  ={md_size, data, orig_len, scan_start, M.leakages} ==> ={M.leakages}.
proof. by proc; sim. qed.

equiv l_final : M.ssl3_cbc_copy_mac_TV_BL ~ M.ssl3_cbc_copy_mac_TV_BL :
  ={M.leakages, md_size, orig_len, out, rec} /\
  (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2}
  ==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_BL; wp.
  call l_rotate_offset_TV; wp.
  call l_init_rotated_mac_stk.
  by inline *; auto.
qed.
