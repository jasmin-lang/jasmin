require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc f (x:W64.t Array1.t, n:W64.t) : W64.t Array1.t = {
    
    var y:W64.t Array1.t;
    y <- witness;
    
    while (((W64.of_int 0) \ult n)) {
      y.[0] <- (W64.of_int 0);
      n <- (n - (W64.of_int 1));
    }
    return (y);
  }
  
  proc main (p:W64.t) : W64.t = {
    
    var r:W64.t;
    var x:W64.t Array1.t;
    x <- witness;
    x <@ f (x, p);
    r <- x.[0];
    return (r);
  }
}.

