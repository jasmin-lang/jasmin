require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array4.
require import WArray16.



module M = {
  proc f (x:W32.t Array4.t) : W32.t Array4.t = {
    var aux: int;
    
    var y:W32.t Array4.t;
    var i:int;
    y <- witness;
    i <- 0;
    while (i < 4) {
      y.[i] <- x.[i];
      i <- i + 1;
    }
    return (y);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux: int;
    
    var f_0:W32.t;
    var j:int;
    var r:W32.t Array4.t;
    r <- witness;
    j <- 0;
    while (j < 4) {
      r.[j] <- a;
      j <- j + 1;
    }
    r <@ f (r);
    f_0 <- r.[0];
    j <- 1;
    while (j < 4) {
      f_0 <- (f_0 `^` r.[j]);
      j <- j + 1;
    }
    return (f_0);
  }
}.

