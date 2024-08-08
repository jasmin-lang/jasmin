require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (p:W64.t) : unit = {
    
    var msf:W64.t;
    var x:W32.t;
    
    msf <- init_msf ;
    x <- (W32.of_int 0);
    x <- protect_32 x msf;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x);
    return ();
  }
}.

