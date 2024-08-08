require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc test (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var t:W64.t Array2.t;
    var p:W64.t;
    t <- witness;
    t.[0] <- (W64.of_int 0);
    t.[1] <- (W64.of_int 1);
    p <- (W64.of_int 0);
    r <- t.[((W64.to_uint p) + 1)];
    return (r);
  }
}.

