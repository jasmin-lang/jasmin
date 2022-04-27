from Jasmin require import JModel.
require import AllCore IntDiv CoreMap List Leakage_models Chacha20_avx2_BL_BL.

clone import Chacha20_avx2_BL_BL.T with theory LeakageModel <-  LeakageModelBL.

equiv chacha20_avx2_ct : M.chacha20_avx2 ~ M.chacha20_avx2 : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}. 
proof. proc;inline *;sim => />. qed.
