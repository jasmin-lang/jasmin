require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.

abbrev g = W32.of_int 540.


module M = {
  var leakages : leakages_t
  
  proc bug_540 () : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var r:W32.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.to_uint g);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (W32.of_int i));
    r <- aux;
    return (r);
  }
}.

