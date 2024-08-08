require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (x:W64.t, y:W64.t) : W64.t * W64.t = {
    
    var r1:W64.t;
    var r2:W64.t;
    
    r1 <- x;
    r2 <- y;
    return (r1, r2);
  }
  
  proc foo2 (x:W64.t, y:W64.t) : W64.t * W64.t = {
    
    var r1:W64.t;
    var r2:W64.t;
    
    r1 <- x;
    r2 <- y;
    return (r1, r2);
  }
  
  proc foo1 (x:W64.t, y:W64.t) : W64.t = {
    
    var r1:W64.t;
    
    r1 <- x;
    return (r1);
  }
}.

