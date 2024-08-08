require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc zero () : W64.t = {
    
    var z:W64.t;
    
    z <- (W64.of_int 0);
    return (z);
  }
}.

