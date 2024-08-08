require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc zero () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array1.t;
    var p:W64.t Array1.t;
    p <- witness;
    s <- witness;
    p <- s;
    p.[0] <- (W64.of_int 0);
    r <- p.[0];
    return (r);
  }
}.

