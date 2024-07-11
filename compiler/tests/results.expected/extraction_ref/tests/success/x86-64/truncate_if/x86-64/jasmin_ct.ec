require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc a (x:W64.t, y:W64.t) : W32.t = {
    var aux: W32.t;
    var aux_0: W64.t;
    
    var z:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- (truncateu32 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \ult (W64.of_int 0)) ? (truncateu32 x) : z);
    z <- aux;
    return (z);
  }
  
  proc b (x:W64.t, y:W64.t) : W32.t = {
    var aux: W32.t;
    var aux_0: W64.t;
    
    var z:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- (truncateu32 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \ult (W64.of_int 0)) ? (truncateu32 x) : z);
    z <- aux;
    return (z);
  }
}.

