require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (p:W64.t, i:W64.t) : W64.t = {
    
    var r:W64.t;
    var x:W64.t;
    
    r <- (loadW64 Glob.mem (W64.to_uint (p + ((W64.of_int 8) * i))));
    x <- (loadW64 Glob.mem (W64.to_uint (p + ((W64.of_int 8) * i))));
    return (r);
  }
}.

