require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.
require Chacha20_ref_TV_CL32.
import StdOrder.IntOrder Ring.IntID.

clone import Chacha20_ref_TV_CL32.T with
theory LeakageModel <-  LeakageModelTVCL32.

equiv chacha20_ref_ct : 
  M.chacha20_ref ~ M.chacha20_ref : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.
