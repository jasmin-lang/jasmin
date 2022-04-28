from Jasmin require import JModel Leakage_models.
require import List Int IntDiv CoreMap Keccak1600_ref_ct.

clone import Keccak1600_ref_ct.T with theory LeakageModel <-  LeakageModelCL32.

equiv ct: M.__keccak1600_ref ~ M.__keccak1600_ref :
 ={inlen,s_out,s_outlen,in_0,s_trail_byte,rate,M.leakages} ==> ={M.leakages}. proof. proc; inline *; sim. qed.
