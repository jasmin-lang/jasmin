from Jasmin require import JModel Leakage_models.
require import AllCore IntDiv CoreMap List Array64 WArray64 Copy_mac_ct.

clone import Copy_mac_ct.T with theory LeakageModel <- LeakageModelBL.

equiv l_final : M.ssl3_cbc_copy_mac_TV_BL ~ M.ssl3_cbc_copy_mac_TV_BL :
  ={M.leakages, md_size, orig_len, out, rec} /\
  (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2}
  ==> ={M.leakages}.
proof.
  proc.
  call (: ={M.leakages, out, md_size} ==> ={M.leakages}); 1: by proc; inline *; sim.
  wp; call (: ={M.leakages, md_size, scan_start} ==> ={M.leakages}); 1: by proc; wp; skip.
  wp; call (: ={ M.leakages, data, scan_start, orig_len, md_size } ==> ={ M.leakages }); 1: by proc; sim.
  by inline *; auto.
qed.
