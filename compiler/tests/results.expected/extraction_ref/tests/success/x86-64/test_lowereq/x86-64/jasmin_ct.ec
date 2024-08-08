require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var r:W64.t;
    var eqf:bool;
    var one:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x = (W64.of_int 0));
    eqf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    one <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (eqf ? one : r);
    r <- aux_0;
    return (r);
  }
}.

