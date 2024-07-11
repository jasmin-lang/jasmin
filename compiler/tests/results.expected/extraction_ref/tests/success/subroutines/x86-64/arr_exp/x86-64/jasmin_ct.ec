require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc test (t:W64.t Array2.t) : W64.t Array2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (t.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    return (t);
  }
  
  proc main () : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array2.t;
    
    var r:W64.t;
    var i:int;
    var t:W64.t Array2.t;
    t <- witness;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ test (t);
    t <- aux_1;
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux_0 <- (t.[0] + t.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- t.[0];
    r <- aux_0;
    return (r);
  }
}.

