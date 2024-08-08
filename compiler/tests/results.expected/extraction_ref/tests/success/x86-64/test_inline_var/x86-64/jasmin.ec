require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc addn (r:W64.t, n:W64.t) : W64.t = {
    
    
    
    r <- (r + n);
    r <- (r + (n + n));
    return (r);
  }
  
  proc f (r1:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- r1;
    r <@ addn (r, (W64.of_int 6));
    r <@ addn (r, (W64.of_int 3));
    r <@ addn (r, (W64.of_int 5));
    return (r);
  }
}.

