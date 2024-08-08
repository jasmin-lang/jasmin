require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc load_small (x:W32.t) : W16.t = {
    
    var r:W16.t;
    var s:W32.t;
    
    s <- x;
    r <- (truncateu16 s);
    return (r);
  }
}.

