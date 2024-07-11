require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (in_0:W64.t) : W64.t = {
    var aux: W32.t;
    var aux_0: W64.t;
    
    var r:W64.t;
    var u:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- in_0;
    u <- (truncateu32 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (u `|>>` (W8.of_int 16));
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (zeroextu64 u);
    r <- aux_0;
    return (r);
  }
}.

