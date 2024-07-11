require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var eqf:bool;
    var one:W64.t;
    
    eqf <- (x = (W64.of_int 0));
    r <- (W64.of_int 0);
    one <- (W64.of_int 1);
    r <- (eqf ? one : r);
    return (r);
  }
}.

