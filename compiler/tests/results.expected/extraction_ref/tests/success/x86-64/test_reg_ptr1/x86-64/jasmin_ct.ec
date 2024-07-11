require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray32.

abbrev glob_t = Array4.of_list witness [W64.of_int 0; W64.of_int 1; W64.of_int 2; W64.of_int 3].


module M = {
  var leakages : leakages_t
  
  proc foo (x:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array4.t;
    
    var r:W64.t;
    var i:int;
    var s:W64.t Array4.t;
    var rt:W64.t Array4.t;
    var st:W64.t Array4.t;
    rt <- witness;
    s <- witness;
    st <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- x;
      leakages <- LeakAddr([i]) :: leakages;
      s.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- s;
    rt <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([0]) :: leakages;
      aux_0 <- (r + rt.[0]);
      r <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- rt;
    st <- aux_1;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([0]) :: leakages;
      aux_0 <- (r + s.[0]);
      r <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- st;
    rt <- aux_1;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      rt.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([0]) :: leakages;
      aux_0 <- (r + rt.[0]);
      r <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- rt;
    s <- aux_1;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([0]) :: leakages;
      aux_0 <- (r + s.[0]);
      r <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
}.

