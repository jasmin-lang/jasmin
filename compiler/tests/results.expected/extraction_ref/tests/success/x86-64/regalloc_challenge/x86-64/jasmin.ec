require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array14.
require import WArray112.



module M = {
  proc main (a:W64.t, b:W64.t) : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var x:W64.t;
    var i:int;
    var z:W64.t Array14.t;
    z <- witness;
    x <- a;
    i <- 0;
    while (i < 14) {
      z.[i] <- (W64.of_int (14 + i));
      i <- i + 1;
    }
    i <- 0;
    while (i < 14) {
      z.[i] <- (z.[i] `|` x);
      i <- i + 1;
    }
    r <- (W64.of_int 42);
    i <- 0;
    while (i < 14) {
      r <- (r `|` z.[i]);
      i <- i + 1;
    }
    return (r);
  }
}.

