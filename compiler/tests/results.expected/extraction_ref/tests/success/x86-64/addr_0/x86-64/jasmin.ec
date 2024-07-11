require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (p:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    r <- (r + (loadW64 Glob.mem (W64.to_uint (p + (- (W64.of_int 8))))));
    return (r);
  }
}.

