require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc test (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var t:W64.t Array2.t;
    var p:W64.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    p <- aux;
    leakages <- LeakAddr([((W64.to_uint p) + 1)]) :: leakages;
    aux <- t.[((W64.to_uint p) + 1)];
    r <- aux;
    return (r);
  }
}.

