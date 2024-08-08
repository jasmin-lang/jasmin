require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array5.
require import WArray20.



module M = {
  var leakages : leakages_t
  
  proc foo () : W32.t = {
    var aux: W32.t;
    
    var z:W32.t;
    var x:W32.t Array5.t;
    x <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    leakages <- LeakAddr([4]) :: leakages;
    x.[4] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    z <- aux;
    return (z);
  }
}.

