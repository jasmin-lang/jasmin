from Jasmin require import JModel.
require import AllCore IntDiv CoreMap List Leakage_models Chacha20_ref_ct.

clone import Chacha20_ref_ct.T with theory LeakageModel <-  LeakageModelTV.

equiv chacha20_ref_ct : M.chacha20_ref ~ M.chacha20_ref : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
