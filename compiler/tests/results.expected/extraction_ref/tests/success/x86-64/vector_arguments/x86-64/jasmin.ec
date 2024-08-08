require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc xor256 (a:W256.t, b:W256.t) : W256.t = {
    
    var r:W256.t;
    
    r <- (a `^` b);
    return (r);
  }
}.

