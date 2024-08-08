require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc f (x:W64.t) : W64.t = {
    
    var e:W64.t;
    var d:W32.t;
    var x1:W32.t;
    var s:W64.t Array1.t;
    var r:W64.t Array1.t;
    var rx:W64.t Array1.t;
    r <- witness;
    rx <- witness;
    s <- witness;
    e <- MOVX_64 x;
    x <- MOVX_64 e;
    e <- x;
    x <- e;
    d <- MOVX_32 (truncateu32 x);
    x1 <- MOVX_32 d;
    x <- (zeroextu64 x1);
    d <- (truncateu32 x);
    x1 <- d;
    x <- (zeroextu64 x1);
    s.[0] <- (W64.of_int 0);
    r <- s;
    r.[0] <- (r.[0] + (W64.of_int 1));
    rx <- r;
    r <- rx;
    r.[0] <- (r.[0] + (W64.of_int 1));
    s <- r;
    x <- (x + s.[0]);
    return (x);
  }
}.

