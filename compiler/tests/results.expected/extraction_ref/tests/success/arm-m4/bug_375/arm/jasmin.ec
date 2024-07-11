require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc main () : W32.t = {
    
    var x:W32.t;
    
    x <- (truncateu32 (invw (W256.of_int 1)));
    return (x);
  }
}.

