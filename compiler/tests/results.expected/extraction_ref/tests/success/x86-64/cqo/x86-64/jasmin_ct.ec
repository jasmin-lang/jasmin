require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_cqo (x:W64.t) : W64.t = {
    var aux: W16.t;
    var aux_1: W32.t;
    var aux_0: W64.t;
    
    var r:W64.t;
    var u:W16.t;
    var v:W16.t;
    var y:W32.t;
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    u <- (truncateu16 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- CQO_16 u;
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- u;
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    y <- (truncateu32 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- CQO_32 y;
    y <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (v `|` (truncateu16 y));
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- CQO_64 z;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (v `|` (truncateu16 z));
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (zeroextu64 v);
    r <- aux_0;
    return (r);
  }
}.

