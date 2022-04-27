from Jasmin require import JModel.
require import AllCore IntDiv CoreMap List Leakage_models Poly1305_ref_ct.

clone import Poly1305_ref_ct.T with theory LeakageModel <-  LeakageModelBL.

equiv poly1305_ref_ct : M.poly1305_ref ~ M.poly1305_ref : ={out, k, inlen, in_0, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
