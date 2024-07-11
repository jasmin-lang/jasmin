require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array128.
require import WArray1024.



module M = {
  var leakages : leakages_t
  
  proc reduce (a:W64.t) : W64.t = {
    var aux: W64.t;
    
    var u:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int ((1 `<<` 18) - 1));
    u <- aux;
    return (u);
  }
  
  proc constant_folding (x:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t;
    var i:int;
    var t:W64.t Array128.t;
    t <- witness;
    leakages <- LeakFor(0,128) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 128) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- x;
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,128) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 128) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- t.[i];
      r <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (r `|>>` (truncateu8 ((W256.of_int i) `&` (W256.of_int 63))));
      r <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- r;
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakFor(0,128) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 128) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- t.[i];
      x <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (r `|` x);
      r <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
}.

