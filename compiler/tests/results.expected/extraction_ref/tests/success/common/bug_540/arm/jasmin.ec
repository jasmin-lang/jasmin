require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.



abbrev g = W32.of_int 540.


module M = {
  proc bug_540 () : W32.t = {
    
    var r:W32.t;
    var i:int;
    
    r <- (W32.of_int 0);
    i <- (W32.to_uint g);
    r <- (r + (W32.of_int i));
    return (r);
  }
}.

