require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array14.
require import WArray112.



module M = {
  var leakages : leakages_t
  
  proc main (a:W64.t, b:W64.t) : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var r:W64.t;
    var x:W64.t;
    var i:int;
    var z:W64.t Array14.t;
    z <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    x <- aux;
    leakages <- LeakFor(0,14) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 14) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int (14 + i));
      leakages <- LeakAddr([i]) :: leakages;
      z.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakFor(0,14) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 14) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (z.[i] `|` x);
      leakages <- LeakAddr([i]) :: leakages;
      z.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 42);
    r <- aux;
    leakages <- LeakFor(0,14) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 14) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (r `|` z.[i]);
      r <- aux;
      i <- i + 1;
    }
    return (r);
  }
}.

