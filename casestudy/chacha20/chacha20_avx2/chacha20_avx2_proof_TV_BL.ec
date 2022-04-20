require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Chacha20_avx2_TV_BL.
import StdOrder.IntOrder Ring.IntID.

clone import Chacha20_avx2_TV_BL.T with
theory LeakageModel <-  LeakageModelTV.

equiv chacha20_avx2_ct :
  M.chacha20_avx2 ~ M.chacha20_avx2 : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
