require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray32.



module M = {
  proc cswap (x:W64.t Array4.t, y:W64.t Array4.t, swap_0:W64.t) : W64.t Array4.t * W64.t Array4.t = {
    var aux: int;
    
    var mask:W64.t;
    var i:int;
    var tmp1:W64.t;
    var tmp2:W64.t;
    
    mask <- (swap_0 * (W64.of_int 18446744073709551615));
    i <- 0;
    while (i < 4) {
      tmp1 <- x.[i];
      tmp1 <- (tmp1 `^` y.[i]);
      tmp1 <- (tmp1 `&` mask);
      x.[i] <- (x.[i] `^` tmp1);
      tmp2 <- y.[i];
      tmp2 <- (tmp2 `^` tmp1);
      y.[i] <- tmp2;
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc swap4 (xp:W64.t, yp:W64.t, swap_0:W64.t, sb:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    var xc:W64.t Array4.t;
    var yc:W64.t Array4.t;
    xc <- witness;
    yc <- witness;
    i <- 0;
    while (i < 4) {
      xc.[i] <- (loadW64 Glob.mem (W64.to_uint (xp + (W64.of_int (8 * i)))));
      yc.[i] <- (loadW64 Glob.mem (W64.to_uint (yp + (W64.of_int (8 * i)))));
      i <- i + 1;
    }
    swap_0 <- (swap_0 `>>` (truncateu8 (sb `&` (W64.of_int 63))));
    (xc, yc) <@ cswap (xc, yc, swap_0);
    i <- 0;
    while (i < 4) {
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (xp + (W64.of_int (8 * i)))) (xc.[i]);
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (yp + (W64.of_int (8 * i)))) (yc.[i]);
      i <- i + 1;
    }
    return ();
  }
}.

