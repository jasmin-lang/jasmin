require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (p:W64.t) : unit = {
    
    
    
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) ((W64.of_int (0 %% 2^32 + 2^32 * 1)));
    return ();
  }
}.

