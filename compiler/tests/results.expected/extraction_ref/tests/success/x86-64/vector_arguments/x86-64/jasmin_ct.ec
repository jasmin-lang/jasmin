require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc xor256 (a:W256.t, b:W256.t) : W256.t = {
    var aux: W256.t;
    
    var r:W256.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a `^` b);
    r <- aux;
    return (r);
  }
}.

