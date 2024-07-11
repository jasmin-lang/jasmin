require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc cswap (x:W64.t Array4.t, y:W64.t Array4.t, swap_0:W64.t) : W64.t Array4.t * W64.t Array4.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var mask:W64.t;
    var i:int;
    var tmp1:W64.t;
    var tmp2:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (swap_0 * (W64.of_int 18446744073709551615));
    mask <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- x.[i];
      tmp1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (tmp1 `^` y.[i]);
      tmp1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp1 `&` mask);
      tmp1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (x.[i] `^` tmp1);
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- y.[i];
      tmp2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp2 `^` tmp1);
      tmp2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- tmp2;
      leakages <- LeakAddr([i]) :: leakages;
      y.[i] <- aux;
      i <- i + 1;
    }
    return (x, y);
  }
  
  proc swap4 (xp:W64.t, yp:W64.t, swap_0:W64.t, sb:W64.t) : unit = {
    var aux: int;
    var aux_0: W64.t;
    var aux_2: W64.t Array4.t;
    var aux_1: W64.t Array4.t;
    
    var i:int;
    var xc:W64.t Array4.t;
    var yc:W64.t Array4.t;
    xc <- witness;
    yc <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([(W64.to_uint (xp + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (xp + (W64.of_int (8 * i)))));
      leakages <- LeakAddr([i]) :: leakages;
      xc.[i] <- aux_0;
      leakages <- LeakAddr([(W64.to_uint (yp + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (yp + (W64.of_int (8 * i)))));
      leakages <- LeakAddr([i]) :: leakages;
      yc.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (swap_0 `>>` (truncateu8 (sb `&` (W64.of_int 63))));
    swap_0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1) <@ cswap (xc, yc, swap_0);
    xc <- aux_2;
    yc <- aux_1;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- xc.[i];
      leakages <- LeakAddr([(W64.to_uint (xp + (W64.of_int (8 * i))))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (xp + (W64.of_int (8 * i)))) (aux_0);
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- yc.[i];
      leakages <- LeakAddr([(W64.to_uint (yp + (W64.of_int (8 * i))))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (yp + (W64.of_int (8 * i)))) (aux_0);
      i <- i + 1;
    }
    return ();
  }
}.

