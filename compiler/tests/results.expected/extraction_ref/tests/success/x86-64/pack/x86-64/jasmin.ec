require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc pack () : W64.t = {
    
    var r:W64.t;
    
    r <- (zeroextu64 (W8.of_int (1 %% 2^1 + 2^1 * (1 %% 2^1 + 2^1 * (1 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * 0)))))))));
    return (r);
  }
}.

