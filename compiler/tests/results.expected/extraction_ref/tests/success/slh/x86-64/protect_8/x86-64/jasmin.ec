require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (p:W64.t) : unit = {
    
    var msf:W64.t;
    var x:W8.t;
    
    msf <- init_msf ;
    x <- (W8.of_int 0);
    x <- protect_8 x msf;
    Glob.mem <- storeW8 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x);
    return ();
  }
}.

