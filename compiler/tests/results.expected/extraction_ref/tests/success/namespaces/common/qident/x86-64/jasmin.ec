require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.



abbrev n__g = W32.of_int 42.


module M = {
  proc main () : W32.t = {
    
    var r:W32.t;
    
    r <- n__g;
    return (r);
  }
}.

