require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (x:W32.t, y:W32.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t;
    
    var lo:W32.t;
    var hi:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- mulu_32 x y;
    hi <- aux_0;
    lo <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (lo `^` hi);
    lo <- aux_0;
    return (lo);
  }
}.

