require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc zero () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array1.t;
    
    var r:W64.t;
    var s:W64.t Array1.t;
    var p:W64.t Array1.t;
    p <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    p.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- p.[0];
    r <- aux_0;
    return (r);
  }
}.

