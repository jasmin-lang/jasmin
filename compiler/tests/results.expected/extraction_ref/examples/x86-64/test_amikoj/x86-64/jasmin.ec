require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t) : W64.t = {
    
    var c:W64.t;
    var a:W64.t;
    var b:W64.t;
    
    a <- x;
    b <- a;
    c <- (b + a);
    return (c);
  }
}.

