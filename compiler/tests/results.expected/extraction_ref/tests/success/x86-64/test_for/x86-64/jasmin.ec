require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f () : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var i:int;
    
    r <- (W64.of_int 0);
    i <- 3;
    while (0 < i) {
      r <- (r + (W64.of_int 1));
      i <- i - 1;
    }
    return (r);
  }
}.

