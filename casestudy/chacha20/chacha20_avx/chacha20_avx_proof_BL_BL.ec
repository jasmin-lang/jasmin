from Jasmin require import JModel.
require import AllCore IntDiv CoreMap List Leakage_models Chacha20_avx_BL_BL.

clone import Chacha20_avx_BL_BL.T with theory LeakageModel <-  LeakageModelBL.

equiv chacha20_avx_ct : M.chacha20_avx ~ M.chacha20_avx : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
