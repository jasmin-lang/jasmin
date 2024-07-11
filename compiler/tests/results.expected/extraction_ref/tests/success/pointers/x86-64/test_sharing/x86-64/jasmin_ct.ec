require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc mul5 (x:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t Array4.t;
    t <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- x;
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (x + t.[i]);
      x <- aux_0;
      i <- i + 1;
    }
    return (x);
  }
  
  proc main (in_0:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- in_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mul5 (x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mul5 (x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mul5 (x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    return (r);
  }
}.

