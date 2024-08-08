require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_lfence () : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to LFENCE *)
    return ();
  }
  
  proc test_mfence () : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to MFENCE *)
    return ();
  }
  
  proc test_sfence () : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to SFENCE *)
    return ();
  }
}.

