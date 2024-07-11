require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array3.
require import WArray24.



module M = {
  var leakages : leakages_t
  
  proc init (p:W64.t Array3.t) : W64.t Array3.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 3) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (p);
  }
  
  proc set (p:W64.t Array3.t) : W64.t Array3.t * W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([0]) :: leakages;
    p.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- p.[1];
    r <- aux;
    return (p, r);
  }
  
  proc foo5 () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array3.t;
    
    var r:W64.t;
    var s:W64.t Array3.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ init (s);
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ set (s);
    s <- aux;
    r <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (r + s.[0]);
    r <- aux_0;
    return (r);
  }
}.

