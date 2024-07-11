require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.

abbrev n__g = W32.of_int 42.


module M = {
  var leakages : leakages_t
  
  proc main () : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- n__g;
    r <- aux;
    return (r);
  }
}.

