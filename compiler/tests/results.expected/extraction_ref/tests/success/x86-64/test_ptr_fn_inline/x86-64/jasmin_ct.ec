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
      aux_0 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (p);
  }
  
  proc foo () : W64.t = {
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W64.t Array3.t;
    
    var r:W64.t;
    var s:W64.t Array3.t;
    var i:int;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ init (s);
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 3) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (r + s.[i]);
      r <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
}.

