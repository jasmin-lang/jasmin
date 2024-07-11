require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test () : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var c:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 42);
    c <- aux;
    leakages <- LeakCond(((W64.of_int 1234) \ule c)) :: LeakAddr([]) :: leakages;
    if (((W64.of_int 1234) \ule c)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 1);
      r <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 0);
      r <- aux;
    }
    return (r);
  }
}.

