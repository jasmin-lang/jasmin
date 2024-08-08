require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array12.
require import WArray96.



module M = {
  var leakages : leakages_t
  
  proc gosub (a:W64.t) : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_5: int;
    var aux_4: W64.t;
    
    var k:W64.t;
    var i:int;
    var tab:W64.t Array12.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
     _4 <- aux;
    k <- aux_4;
    leakages <- LeakFor(0,12) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 12) {
      leakages <- LeakAddr([]) :: leakages;
      aux_4 <- a;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux_4;
      i <- i + 1;
    }
    leakages <- LeakFor(0,12) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 12) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_4 <- (k + tab.[i]);
      k <- aux_4;
      i <- i + 1;
    }
    return (k);
  }
  
  proc main (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var t:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ gosub (x);
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + t);
    r <- aux;
    return (r);
  }
}.

