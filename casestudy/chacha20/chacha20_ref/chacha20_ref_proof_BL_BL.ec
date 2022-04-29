from Jasmin require import JModel Leakage_models.
require import AllCore IntDiv CoreMap List Chacha20_ref_ct.

clone import Chacha20_ref_ct.T with theory LeakageModel <-  LeakageModelBL.

equiv chacha20_ref_ct : M.chacha20_ref ~ M.chacha20_ref : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
