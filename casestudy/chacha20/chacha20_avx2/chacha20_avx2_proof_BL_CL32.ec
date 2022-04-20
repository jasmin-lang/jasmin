require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Chacha20_avx2_BL_CL32.
import StdOrder.IntOrder Ring.IntID.

clone import Chacha20_avx2_BL_CL32.T with
theory LeakageModel <-  LeakageModelCL32.

equiv chacha20_avx2_ct :
  M.chacha20_avx2 ~ M.chacha20_avx2 : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}. proof. proc;inline *;sim => />. qed.
