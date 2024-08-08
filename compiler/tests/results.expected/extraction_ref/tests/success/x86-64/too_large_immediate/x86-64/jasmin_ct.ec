require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main () : W64.t = {
    var aux: W64.t;
    
    var res_0:W64.t;
    var s:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 10000000000);
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    res_0 <- aux;
    return (res_0);
  }
}.

