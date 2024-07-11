require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc f (x:W32.t Array4.t) : W32.t Array4.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var y:W32.t Array4.t;
    var i:int;
    y <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- x.[i];
      leakages <- LeakAddr([i]) :: leakages;
      y.[i] <- aux_0;
      i <- i + 1;
    }
    return (y);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux: int;
    var aux_0: W32.t;
    var aux_1: W32.t Array4.t;
    
    var f_0:W32.t;
    var j:int;
    var r:W32.t Array4.t;
    r <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- a;
      leakages <- LeakAddr([j]) :: leakages;
      r.[j] <- aux_0;
      j <- j + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ f (r);
    r <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r.[0];
    f_0 <- aux_0;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    j <- 1;
    while (j < 4) {
      leakages <- LeakAddr([j]) :: leakages;
      aux_0 <- (f_0 `^` r.[j]);
      f_0 <- aux_0;
      j <- j + 1;
    }
    return (f_0);
  }
}.

