require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc swap_0 (u:W64.t Array2.t) : W64.t Array2.t = {
    
    var z:W64.t Array2.t;
    z <- witness;
    z.[1] <- u.[0];
    z.[0] <- u.[1];
    return (z);
  }
  
  proc f () : W64.t = {
    
    var r:W64.t;
    var x:W64.t Array2.t;
    var y:W64.t Array2.t;
    x <- witness;
    y <- witness;
    x.[1] <- (W64.of_int 1);
    x.[0] <- (W64.of_int 0);
    y <@ swap_0 (x);
    x <- copy_64 y;
    r <- x.[0];
    return (r);
  }
}.

