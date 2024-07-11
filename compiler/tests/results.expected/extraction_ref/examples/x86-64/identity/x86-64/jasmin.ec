require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc identity (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    return (r);
  }
}.

