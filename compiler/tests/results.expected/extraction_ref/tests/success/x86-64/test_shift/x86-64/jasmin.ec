require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array128.
require import WArray1024.



module M = {
  proc reduce (a:W64.t) : W64.t = {
    
    var u:W64.t;
    
    u <- (W64.of_int ((1 `<<` 18) - 1));
    return (u);
  }
  
  proc constant_folding (x:W64.t) : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var i:int;
    var t:W64.t Array128.t;
    t <- witness;
    i <- 0;
    while (i < 128) {
      t.[i] <- x;
      i <- i + 1;
    }
    i <- 0;
    while (i < 128) {
      r <- t.[i];
      r <- (r `|>>` (truncateu8 ((W256.of_int i) `&` (W256.of_int 63))));
      t.[i] <- r;
      i <- i + 1;
    }
    r <- (W64.of_int 0);
    i <- 0;
    while (i < 128) {
      x <- t.[i];
      r <- (r `|` x);
      i <- i + 1;
    }
    return (r);
  }
}.

