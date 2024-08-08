require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc zero () : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    z <- aux;
    return (z);
  }
}.

