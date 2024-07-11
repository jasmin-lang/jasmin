require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc foo () : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var s:W64.t Array2.t;
    var p:W64.t Array2.t;
    var i:int;
    var s1:W64.t Array2.t;
    p <- witness;
    s <- witness;
    s1 <- witness;
    p <- s;
    i <- 0;
    while (i < 2) {
      p.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    s1 <- p;
    r <- (W64.of_int 0);
    i <- 0;
    while (i < 2) {
      r <- (r + s1.[i]);
      i <- i + 1;
    }
    return (r);
  }
}.

