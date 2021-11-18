require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array128 WArray128.

require Copy_mac_ct.
require import Leakage_models.

clone import Copy_mac_ct.T as T_TV with
theory LeakageModel <- LeakageModelTV.

clone import Copy_mac_ct.T as T_BL with
theory LeakageModel <- LeakageModelCL.

import BitEncoding.BS2Int.

equiv l_final_final : T_BL.M.ssl3_cbc_copy_mac_BL_BL ~ M.ssl3_cbc_copy_mac_BL_BL.
  M.ssl3_cbc_copy_mac_TV_BL ~ M.ssl3_cbc_copy_mac_TV_BL.
proof.
  proc.
  call l_rotate_mac_BL; wp.
  call l_rotate_offset_BL; wp.
  while (={i, j, orig_len, data, zero, md_size, M.leakages}); 1: by inline*;sim.
  wp; skip => |> &1 &2. 
qed.

equiv l_final : M.ssl3_cbc_copy_mac_TV_BL ~ M.ssl3_cbc_copy_mac_TV_BL :
={M.leakages, md_size, orig_len, out, rec} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = 
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2} /\
16 <= to_uint md_size{2} <= 64 /\
(wf_rec Glob.mem rec orig_len md_size){1} /\ 
(wf_rec Glob.mem rec orig_len md_size){2}  
==> ={M.leakages}.
