require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Chacha20_avx_BL_CL64.
import StdOrder.IntOrder Ring.IntID.

clone import Chacha20_avx_BL_CL64.T with
theory LeakageModel <-  LeakageModelCL.

equiv chacha20_avx_ct :
  M.chacha20_avx ~ M.chacha20_avx : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
