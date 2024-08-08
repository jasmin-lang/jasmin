require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main () : W64.t = {
    
    var res_0:W64.t;
    var s:W64.t;
    
    s <- (W64.of_int 10000000000);
    res_0 <- s;
    return (res_0);
  }
}.

