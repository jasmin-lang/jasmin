require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc load_small (x:W32.t) : W16.t = {
    var aux_0: W16.t;
    var aux: W32.t;
    
    var r:W16.t;
    var s:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    r <- (truncateu16 aux);
    return (r);
  }
}.

