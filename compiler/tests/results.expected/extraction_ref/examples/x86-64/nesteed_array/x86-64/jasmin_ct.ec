require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array256.
require import WArray2048.



module M = {
  var leakages : leakages_t
  
  proc foo (x:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t;
    var j:int;
    var i:int;
    var a:W64.t Array256.t;
    a <- witness;
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
      j <- 0;
      while (j < 8) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        leakages <- LeakAddr([((8 * i) + j)]) :: leakages;
        a.[((8 * i) + j)] <- aux_0;
        j <- j + 1;
      }
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakFor(0,256) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 256) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (r + a.[i]);
      r <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
}.

