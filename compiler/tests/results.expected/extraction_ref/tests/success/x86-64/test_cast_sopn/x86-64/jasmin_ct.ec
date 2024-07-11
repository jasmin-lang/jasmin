require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo (x:W128.t, y:W128.t) : W256.t = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var z:W256.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPAND_128 x y;
    z <- zeroextu256(aux);
    return (z);
  }
}.

