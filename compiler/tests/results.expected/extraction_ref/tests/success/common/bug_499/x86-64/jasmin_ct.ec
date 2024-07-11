require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array8.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc aux (out:W32.t Array2.t, in_0:W32.t Array2.t) : W32.t Array2.t = {
    var aux_3: W32.t;
    var aux_2: W32.t;
    var aux_0: W8.t Array8.t;
    var aux_1: W32.t Array2.t;
    
    var x:W32.t Array2.t;
    var y:W32.t Array2.t;
    x <- witness;
    y <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- copy_32 in_0;
    x <- aux_1;
    leakages <- LeakAddr([1; 0]) :: leakages;
    (aux_3, aux_2) <- mulu_32 x.[0] x.[1];
    leakages <- LeakAddr([0]) :: leakages;
    y.[0] <- aux_3;
    leakages <- LeakAddr([1]) :: leakages;
    y.[1] <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- copy_32 y;
    out <- aux_1;
    return (out);
  }
  
  proc test (t:W32.t) : W32.t = {
    var aux_0: int;
    var aux_1: W32.t;
    var aux_2: W32.t Array2.t;
    
    var res_0:W32.t;
    var i:int;
    var a:W32.t Array2.t;
    var b:W32.t Array2.t;
    a <- witness;
    b <- witness;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <@ aux (b, a);
    b <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W32.of_int 0);
    res_0 <- aux_1;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_1 <- b.[i];
      t <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (res_0 `|` t);
      res_0 <- aux_1;
      i <- i + 1;
    }
    return (res_0);
  }
}.

