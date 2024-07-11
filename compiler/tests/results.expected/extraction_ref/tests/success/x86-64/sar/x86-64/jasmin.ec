require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (in_0:W64.t) : W64.t = {
    
    var r:W64.t;
    var u:W32.t;
    
    u <- (truncateu32 in_0);
    u <- (u `|>>` (W8.of_int 16));
    r <- (zeroextu64 u);
    return (r);
  }
}.

