require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc add (x:W32.t, y:W32.t) : W32.t = {
    
    var r:W32.t;
    
    r <- (x + y);
    return (r);
  }
}.

