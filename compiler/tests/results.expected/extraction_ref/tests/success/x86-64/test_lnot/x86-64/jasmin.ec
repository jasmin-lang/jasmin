require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (r1:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r1 <- (invw r1);
    r <- r1;
    r <- (truncateu64 (invw (W256.of_int 17)));
    return (r);
  }
  
  proc g (r1:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- r1;
    r <- (invw r);
    return (r);
  }
}.

