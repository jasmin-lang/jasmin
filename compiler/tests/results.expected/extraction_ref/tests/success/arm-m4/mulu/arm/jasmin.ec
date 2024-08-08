require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc test (x:W32.t, y:W32.t) : W32.t = {
    
    var lo:W32.t;
    var hi:W32.t;
    
    (hi, lo) <- mulu_32 x y;
    lo <- (lo `^` hi);
    return (lo);
  }
}.

