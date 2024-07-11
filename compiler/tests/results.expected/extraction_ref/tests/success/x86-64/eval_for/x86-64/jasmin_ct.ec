require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array12.
require import WArray96.



module M = {
  var leakages : leakages_t
  
  proc test_for () : W64.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var sum:W64.t;
    var i:int;
    var t:W64.t Array12.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    t <- witness;
    leakages <- LeakFor(0,12) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 12) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- set0_64 ;
    _of_ <- aux_5;
    _cf_ <- aux_4;
    _sf_ <- aux_3;
     _0 <- aux_2;
    _zf_ <- aux_1;
    sum <- aux_0;
    leakages <- LeakFor(0,12) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 12) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (sum + t.[i]);
      sum <- aux_0;
      i <- i + 1;
    }
    return (sum);
  }
}.

