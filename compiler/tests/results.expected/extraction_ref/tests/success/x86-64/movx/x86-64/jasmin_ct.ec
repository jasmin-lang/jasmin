require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : W64.t = {
    var aux_0: W32.t;
    var aux: W64.t;
    var aux_1: W64.t Array1.t;
    
    var e:W64.t;
    var d:W32.t;
    var x1:W32.t;
    var s:W64.t Array1.t;
    var r:W64.t Array1.t;
    var rx:W64.t Array1.t;
    r <- witness;
    rx <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVX_64 x;
    e <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVX_64 e;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    e <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- e;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVX_32 (truncateu32 x);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVX_32 d;
    x1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu64 x1);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    d <- (truncateu32 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- d;
    x1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu64 x1);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- s;
    r <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r.[0] + (W64.of_int 1));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- r;
    rx <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- rx;
    r <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r.[0] + (W64.of_int 1));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- r;
    s <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x + s.[0]);
    x <- aux;
    return (x);
  }
}.

