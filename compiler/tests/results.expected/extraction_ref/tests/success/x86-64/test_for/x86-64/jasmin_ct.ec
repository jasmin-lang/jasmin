require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f () : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var r:W64.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakFor(3,0) :: LeakAddr([]) :: leakages;
    i <- 3;
    while (0 < i) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (r + (W64.of_int 1));
      r <- aux;
      i <- i - 1;
    }
    return (r);
  }
}.

