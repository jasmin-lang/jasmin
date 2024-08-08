require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (r1:W64.t, r2:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((W64.of_int (- 3)) + r1);
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((W64.of_int 2) * r1) - (W64.of_int 10));
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((r2 + ((W64.of_int 4) * r1)) - (W64.of_int 15));
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((W64.of_int 2) * r1) + (W64.of_int (- 17)));
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    r <- aux;
    return (r);
  }
}.

