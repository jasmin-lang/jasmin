require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f1 (x:W64.t) : W64.t = {
    
    
    
    x <- (x + (W64.of_int 1));
    return (x);
  }
  
  proc f2 (x:W64.t) : W64.t = {
    
    
    
    x <- (x + (W64.of_int 2));
    return (x);
  }
  
  proc foo (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    x <@ f1 (x);
    x <@ f2 (x);
    x <@ f1 (x);
    r <- x;
    return (r);
  }
}.

