require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc add1 (arg:W64.t) : W64.t = {
    
    var z:W64.t;
    
    z <- arg;
    z <- (z + (W64.of_int 1));
    return (z);
  }
}.

