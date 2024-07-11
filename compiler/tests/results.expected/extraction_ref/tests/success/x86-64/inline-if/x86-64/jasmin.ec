require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test () : W64.t = {
    
    var r:W64.t;
    var c:W64.t;
    
    c <- (W64.of_int 42);
    if (((W64.of_int 1234) \ule c)) {
      r <- (W64.of_int 1);
    } else {
      r <- (W64.of_int 0);
    }
    return (r);
  }
}.

