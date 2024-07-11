require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc loop (x:W64.t) : W64.t = {
    
    var s:W64.t Array1.t;
    var p:W64.t Array1.t;
    var sp_0:W64.t Array1.t;
    var y:W64.t;
    p <- witness;
    s <- witness;
    sp_0 <- witness;
    s.[0] <- x;
    p <- s;
    sp_0 <- p;
    y <- (W64.of_int 0);
    
    while ((y \ult (W64.of_int 42))) {
      p <- sp_0;
      p.[0] <- (p.[0] + x);
      x <- (x + p.[0]);
      sp_0 <- p;
      y <- (y + (W64.of_int 1));
    }
    p <- sp_0;
    s <- p;
    x <- s.[0];
    return (x);
  }
  
  proc test (x:W64.t) : W64.t = {
    
    var z:W64.t;
    
    z <@ loop (x);
    return (z);
  }
}.

