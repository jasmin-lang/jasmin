require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.



abbrev __38 = W64.of_int 38.


module M = {
  proc main (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    r <- (r * __38);
    return (r);
  }
}.

