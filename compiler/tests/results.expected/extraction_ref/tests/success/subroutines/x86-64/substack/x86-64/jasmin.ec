require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc double (x:W64.t) : W64.t = {
    
    var y:W64.t;
    
    y <- x;
    x <- (x + y);
    return (x);
  }
  
  proc main (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    r <@ double (r);
    r <@ double (r);
    return (r);
  }
}.

