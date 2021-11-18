require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array128 WArray128.

require Copy_mac_ct.
require import Leakage_models.

clone import Copy_mac_ct.T with
theory LeakageModel <- LeakageModelCL.

import BitEncoding.BS2Int.

equiv l_rotate_offset_BL : M.rotate_offset_BL ~ M.rotate_offset_BL:
={M.leakages, md_size, scan_start}
==> ={M.leakages}.
proof. by proc; wp; skip. qed.

equiv l_rotate_mac_BL : M.rotate_mac_BL ~ M.rotate_mac_BL : ={M.leakages, out, md_size} ==> ={M.leakages}.
proof. by proc; inline *; sim. qed.

equiv l_init_rotated_mac_stk : M.init_rotated_mac_stk ~ M.init_rotated_mac_stk :
  ={ M.leakages, data, scan_start, orig_len, md_size } ==> ={ M.leakages }.
proof.
  proc; wp.
  while (={ M.leakages, data, orig_len, md_size, zero, i, j }); first by sim.
  by wp; skip.
qed.

equiv l_init_scan_start : M.init_scan_start ~ M.init_scan_start :
  ={ M.leakages, rec, orig_len, md_size }
  /\ (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2}
  ==> ={ M.leakages } /\ res.`1{1} = res.`1{2} /\ res.`2{1} = res.`2{2}.
proof. by proc; wp; skip. qed.

equiv l_final : M.ssl3_cbc_copy_mac_BL_BL ~ M.ssl3_cbc_copy_mac_BL_BL :
={M.leakages, md_size, orig_len, out, rec} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} =
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2}
==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_BL; wp.
  call l_rotate_offset_BL; wp.
  call l_init_rotated_mac_stk; wp.
  by call l_init_scan_start; auto.
qed.
