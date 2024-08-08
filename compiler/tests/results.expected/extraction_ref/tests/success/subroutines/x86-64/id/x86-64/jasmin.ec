require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc id (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    return (r);
  }
  
  proc a (x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <@ id (y);
    r <- (r + x);
    return (r);
  }
}.

