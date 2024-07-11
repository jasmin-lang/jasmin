require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array7 Array8.
require import WArray56 WArray64.



module M = {
  var leakages : leakages_t
  
  proc zero () : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var x:W64.t;
    var i:int;
    var t:W64.t Array7.t;
    t <- witness;
    leakages <- LeakFor(0,7) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 7) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    x <- aux_0;
    leakages <- LeakFor(0,7) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 7) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (x + t.[i]);
      x <- aux_0;
      i <- i + 1;
    }
    return (x);
  }
  
  proc one () : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var y:W64.t;
    var i:int;
    var t:W64.t Array8.t;
    var x:W64.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    y <- aux;
    leakages <- LeakFor(0,(7 + 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- (7 + 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x <- aux;
    leakages <- LeakFor(0,(7 + 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- (7 + 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (x + t.[i]);
      x <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y + x);
    y <- aux;
    return (y);
  }
}.

