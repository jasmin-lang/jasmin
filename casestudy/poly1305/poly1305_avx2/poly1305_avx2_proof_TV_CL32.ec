from Jasmin require import JModel.
require import AllCore IntDiv CoreMap List Leakage_models Poly1305_avx2_ct.

clone import Poly1305_avx2_ct.T with theory LeakageModel <-  LeakageModelTVCL32.

equiv poly1305_avx2_CT : M.poly1305_avx2 ~ M.poly1305_avx2 : 
  ={k, in_0, out, inlen, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim. qed.
