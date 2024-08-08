require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4 Array32.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc test (x:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W8.t Array32.t;
    var aux_2: W64.t Array4.t;
    
    var q:W64.t;
    var i:int;
    var s:W64.t Array4.t;
    var r:W64.t Array4.t;
    r <- witness;
    s <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- x;
      leakages <- LeakAddr([i]) :: leakages;
      s.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- copy_64 s;
    r <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    q <- aux_0;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (q + r.[i]);
      q <- aux_0;
      i <- i + 1;
    }
    return (q);
  }
}.

