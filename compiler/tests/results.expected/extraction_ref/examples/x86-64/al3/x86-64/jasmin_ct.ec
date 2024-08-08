require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array16.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc swap_0 (u:W64.t Array2.t) : W64.t Array2.t = {
    var aux: W64.t;
    
    var z:W64.t Array2.t;
    z <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- u.[0];
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- u.[1];
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    return (z);
  }
  
  proc f () : W64.t = {
    var aux: W64.t;
    var aux_1: W8.t Array16.t;
    var aux_0: W64.t Array2.t;
    
    var r:W64.t;
    var x:W64.t Array2.t;
    var y:W64.t Array2.t;
    x <- witness;
    y <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ swap_0 (x);
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_64 y;
    x <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    r <- aux;
    return (r);
  }
}.

