require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array8.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc foo (x:W64.t) : W64.t = {
    var aux_1: W64.t;
    var aux_0: W8.t Array8.t;
    var aux: W64.t Array1.t;
    
    var t:W64.t Array1.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- t.[0];
    x <- aux_1;
    return (x);
  }
}.

