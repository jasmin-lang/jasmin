require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f1 (x:W64.t) : W64.t = {
    
    
    
    x <- (x + (W64.of_int 1));
    return (x);
  }
  
  proc f2 (x:W64.t) : W64.t = {
    
    
    
    
    return (x);
  }
  
  proc good () : W64.t = {
    
    var r:W64.t;
    var t:W64.t;
    var x:W64.t;
    
    t <- (W64.of_int 1);
    x <@ f2 (t);
    r <- t;
    r <- (r + x);
    return (r);
  }
}.

