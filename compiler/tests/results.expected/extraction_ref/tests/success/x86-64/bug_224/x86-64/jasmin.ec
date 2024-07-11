require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (x:W64.t) : unit = {
    
    
    
    x <- (x - (W64.of_int 1));
    while (((W64.of_int 0) \ult x)) {
      x <- (x - (W64.of_int 1));
    }
    return ();
  }
}.

