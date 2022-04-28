require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.
require import Chacha20_avx2_ct.
import StdOrder.IntOrder Ring.IntID.

clone import Chacha20_avx2_ct.T with
theory LeakageModel <-  LeakageModelTVCL32.

equiv chacha20_avx2_ct :
  M.chacha20_avx2 ~ M.chacha20_avx2 : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
