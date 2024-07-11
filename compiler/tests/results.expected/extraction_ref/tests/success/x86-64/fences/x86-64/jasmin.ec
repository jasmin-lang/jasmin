require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_lfence () : unit = {
    
    
    
    (* Erased call to LFENCE *)
    return ();
  }
  
  proc test_mfence () : unit = {
    
    
    
    (* Erased call to MFENCE *)
    return ();
  }
  
  proc test_sfence () : unit = {
    
    
    
    (* Erased call to SFENCE *)
    return ();
  }
}.

