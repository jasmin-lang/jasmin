require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc add1 (arg:W64.t) : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- arg;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (z + (W64.of_int 1));
    z <- aux;
    return (z);
  }
}.

