require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (p:W64.t) : unit = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int (0 %% 2^32 + 2^32 * 1));
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
}.

