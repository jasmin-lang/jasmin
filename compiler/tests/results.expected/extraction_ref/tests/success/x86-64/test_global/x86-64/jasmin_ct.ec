require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.

abbrev __38 = W64.of_int 38.


module M = {
  var leakages : leakages_t
  
  proc main (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r * __38);
    r <- aux;
    return (r);
  }
}.

