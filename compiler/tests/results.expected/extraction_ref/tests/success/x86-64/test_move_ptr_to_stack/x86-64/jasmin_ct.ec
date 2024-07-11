require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc foo () : W64.t = {
    var aux_0: int;
    var aux_1: W64.t;
    var aux: W64.t Array2.t;
    
    var r:W64.t;
    var s:W64.t Array2.t;
    var p:W64.t Array2.t;
    var i:int;
    var s1:W64.t Array2.t;
    p <- witness;
    s <- witness;
    s1 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    p <- aux;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- p;
    s1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W64.of_int 0);
    r <- aux_1;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_1 <- (r + s1.[i]);
      r <- aux_1;
      i <- i + 1;
    }
    return (r);
  }
}.

