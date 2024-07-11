require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main () : W32.t = {
    var aux: W32.t;
    var aux_0: W256.t;
    
    var x:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (invw (W256.of_int 1));
    x <- (truncateu32 aux_0);
    return (x);
  }
}.

