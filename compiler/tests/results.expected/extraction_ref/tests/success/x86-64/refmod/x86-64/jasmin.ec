require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    
    x <- x;
    r <- (W64.of_int 1);
    y <- ((y \ule (W64.of_int 0)) ? r : y);
    r <- (x \umod y);
    r <- r;
    return (r);
  }
}.

