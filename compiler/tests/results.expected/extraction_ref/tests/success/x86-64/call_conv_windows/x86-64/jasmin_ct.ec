require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array16.
require import WArray512.



module M = {
  var leakages : leakages_t
  
  proc foo () : W256.t = {
    var aux: int;
    var aux_0: W256.t;
    
    var xmm0:W256.t;
    var i:int;
    var xmm:W256.t Array16.t;
    xmm <- witness;
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 16) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- set0_256 ;
      leakages <- LeakAddr([i]) :: leakages;
      xmm.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 16) {
      leakages <- LeakAddr([i; 0]) :: leakages;
      aux_0 <- (xmm.[0] `^` xmm.[i]);
      leakages <- LeakAddr([0]) :: leakages;
      xmm.[0] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- xmm.[0];
    xmm0 <- aux_0;
    return (xmm0);
  }
}.

