require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray8.



module M = {
  proc main (x:W32.t, y:W32.t) : W32.t = {
    
    var t:W32.t Array2.t;
    var p:W32.t Array2.t;
    var z:W32.t;
    p <- witness;
    t <- witness;
    p <- t;
    z <- (W32.of_int 0);
    p.[0] <- z;
    z <- (z + (W32.of_int 1));
    p.[1] <- z;
    (* Erased call to spill *)
    x <- (x + y);
    (* Erased call to unspill *)
    z <- p.[0];
    x <- (x + z);
    z <- p.[1];
    x <- (x + z);
    x <- x;
    return (x);
  }
}.

