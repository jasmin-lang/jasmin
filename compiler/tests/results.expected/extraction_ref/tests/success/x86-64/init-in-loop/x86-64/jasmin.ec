require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main () : W64.t = {
    
    var y:W64.t;
    var x:W64.t;
    
    x <- (W64.of_int 2);
    
    while (((W64.of_int 0) \ult x)) {
      y <- (W64.of_int 1);
      x <- (x - (W64.of_int 1));
    }
    return (y);
  }
}.

