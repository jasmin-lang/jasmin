from Jasmin require import JModel.
require import AllCore IntDiv CoreMap List Leakage_models Poly1305_avx_ct.

clone import Poly1305_avx_ct.T with theory LeakageModel <-  LeakageModelBL.

equiv chacha20_avx2_ct : M.poly1305_avx ~ M.poly1305_avx : ={out, k, inlen, in_0,M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
