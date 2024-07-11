require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc loop (x:W64.t) : W64.t = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var s:W64.t Array1.t;
    var p:W64.t Array1.t;
    var sp_0:W64.t Array1.t;
    var y:W64.t;
    p <- witness;
    s <- witness;
    sp_0 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- p;
    sp_0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    y <- aux;
    
    leakages <- LeakCond((y \ult (W64.of_int 42))) :: LeakAddr([]) :: leakages;
    
    while ((y \ult (W64.of_int 42))) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- sp_0;
      p <- aux_0;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- (p.[0] + x);
      leakages <- LeakAddr([0]) :: leakages;
      p.[0] <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- (x + p.[0]);
      x <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- p;
      sp_0 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (y + (W64.of_int 1));
      y <- aux;
    leakages <- LeakCond((y \ult (W64.of_int 42))) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- sp_0;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- p;
    s <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s.[0];
    x <- aux;
    return (x);
  }
  
  proc test (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ loop (x);
    z <- aux;
    return (z);
  }
}.

