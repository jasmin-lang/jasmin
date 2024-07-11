require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc flush (p:W64.t) : unit = {
    
    
    
    (* Erased call to CLFLUSH *)
    return ();
  }
}.

