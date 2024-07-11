require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc pack () : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu64 (W8.of_int (1 %% 2^1 + 2^1 * (1 %% 2^1 + 2^1 * (1 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * (0 %% 2^1 + 2^1 * 0)))))))));
    r <- aux;
    return (r);
  }
}.

