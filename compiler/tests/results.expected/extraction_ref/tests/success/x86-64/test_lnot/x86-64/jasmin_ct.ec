require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (r1:W64.t) : W64.t = {
    var aux: W64.t;
    var aux_0: W256.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (invw r1);
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (invw (W256.of_int 17));
    r <- (truncateu64 aux_0);
    return (r);
  }
  
  proc g (r1:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (invw r);
    r <- aux;
    return (r);
  }
}.

