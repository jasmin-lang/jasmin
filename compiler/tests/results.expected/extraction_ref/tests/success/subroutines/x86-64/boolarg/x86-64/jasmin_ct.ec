require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array8.
require import WArray64.



module M = {
  var leakages : leakages_t
  
  proc zero (b:bool) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var sum:W64.t;
    var i:int;
    var t:W64.t Array8.t;
    t <- witness;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int i);
      sum <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (b ? sum : t.[i]);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    sum <- aux_0;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (sum + t.[i]);
      sum <- aux_0;
      i <- i + 1;
    }
    return (sum);
  }
  
  proc main (x:W64.t) : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var result:W64.t;
    var b:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux) <- TEST_64 x x;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <@ zero (b);
    result <- aux_4;
    return (result);
  }
}.

