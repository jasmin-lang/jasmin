from Jasmin require import JModel.
require import List Int IntDiv CoreMap Leakage_models Keccak1600_ref_ct.

clone import Keccak1600_ref_ct.T with theory LeakageModel <-  LeakageModelTVCL32.

equiv ct: 
  M.__keccak1600_ref ~ M.__keccak1600_ref :
     ={inlen,s_out,s_outlen,in_0,s_trail_byte,rate,M.leakages} ==> ={M.leakages}.
proof. proc; inline *; sim. qed.
