from Jasmin require import JModel Leakage_models.
require import List Int IntDiv CoreMap Keccak1600_scalar_ct.

clone import Keccak1600_scalar_ct.T with theory LeakageModel <-  LeakageModelTVCL32.

equiv ct:
  M.__keccak1600_scalar ~ M.__keccak1600_scalar :
     ={inlen,s_outlen,M.leakages,rate,in_0,s_out,iotas} ==> ={M.leakages}.
proof. proc; inline *; sim. qed.