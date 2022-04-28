from Jasmin require import JModel Leakage_models.
require import AllCore IntDiv CoreMap List Chacha20_avx_ct.

clone import Chacha20_avx_ct.T with theory LeakageModel <-  LeakageModelCL32.

equiv chacha20_avx_ct : M.chacha20_avx ~ M.chacha20_avx : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
