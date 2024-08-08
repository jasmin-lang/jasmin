require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc flush (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to CLFLUSH *)
    return ();
  }
}.

