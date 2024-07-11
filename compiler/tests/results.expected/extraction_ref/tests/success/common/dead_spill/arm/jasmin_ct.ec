require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (x:W32.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to spill *)
    return ();
  }
}.

