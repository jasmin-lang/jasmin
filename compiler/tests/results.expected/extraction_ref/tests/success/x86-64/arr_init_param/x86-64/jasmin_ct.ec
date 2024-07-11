require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array12 Array96.
require import WArray96.



module M = {
  var leakages : leakages_t
  
  proc test () : W64.t = {
    var aux_1: int;
    var aux_2: W64.t;
    var aux_0: W8.t Array96.t;
    var aux: W64.t Array12.t;
    
    var r:W64.t;
    var t:W64.t Array12.t;
    var i:int;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    t <- witness;
    leakages <- LeakFor(0,(10 + 2)) :: LeakAddr([]) :: leakages;
    aux_1 <- (10 + 2);
    i <- 0;
    while (i < aux_1) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_2;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (W64.of_int 0);
    r <- aux_2;
    leakages <- LeakFor(0,(10 + 2)) :: LeakAddr([]) :: leakages;
    aux_1 <- (10 + 2);
    i <- 0;
    while (i < aux_1) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_2 <- (r + t.[i]);
      r <- aux_2;
      i <- i + 1;
    }
    return (r);
  }
}.

