require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (x:W32.t, y:W32.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- swap_ x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x <- aux_0;
    return (x);
  }
}.

