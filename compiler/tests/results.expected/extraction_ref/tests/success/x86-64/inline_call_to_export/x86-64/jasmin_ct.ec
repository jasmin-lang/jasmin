require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc sum (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- LEA_64 (x + y);
    z <- aux;
    return (z);
  }
}.

