require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc main (x:W32.t, y:W32.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t Array2.t;
    
    var t:W32.t Array2.t;
    var p:W32.t Array2.t;
    var z:W32.t;
    p <- witness;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([0]) :: leakages;
    p.[0] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (z + (W32.of_int 1));
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([1]) :: leakages;
    p.[1] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to spill *)
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x + y);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to unspill *)
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- p.[0];
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x + z);
    x <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- p.[1];
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x + z);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x <- aux_0;
    return (x);
  }
}.

