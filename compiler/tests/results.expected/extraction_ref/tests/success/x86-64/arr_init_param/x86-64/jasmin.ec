require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array12.
require import WArray96.



module M = {
  proc test () : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var t:W64.t Array12.t;
    var i:int;
    t <- witness;
    t <- witness;
    aux <- (10 + 2);
    i <- 0;
    while (i < aux) {
      t.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    r <- (W64.of_int 0);
    aux <- (10 + 2);
    i <- 0;
    while (i < aux) {
      r <- (r + t.[i]);
      i <- i + 1;
    }
    return (r);
  }
}.

