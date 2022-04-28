require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.
require import Chacha20_avx_ct.
import StdOrder.IntOrder Ring.IntID.

clone import Chacha20_avx_ct.T with
theory LeakageModel <-  LeakageModelCL.

equiv chacha20_avx_ct :
  M.chacha20_avx ~ M.chacha20_avx : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
