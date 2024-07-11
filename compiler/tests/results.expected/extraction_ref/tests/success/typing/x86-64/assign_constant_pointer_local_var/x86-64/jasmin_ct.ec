require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc main () : W64.t = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var a:W64.t;
    var s:W64.t Array1.t;
    var p:W64.t Array1.t;
    p <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 42);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s;
    p <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s.[0];
    a <- aux;
    return (a);
  }
}.

