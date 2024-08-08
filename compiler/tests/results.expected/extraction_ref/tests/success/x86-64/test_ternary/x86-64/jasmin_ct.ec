require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array8.
require import WArray64.



module M = {
  var leakages : leakages_t
  
  proc test_cmp (x:W64.t, y:W64.t) : W64.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t;
    var i:int;
    var t:W64.t Array8.t;
    var of_0:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var e:bool;
    var b:bool;
    var be:bool;
    var l:bool;
    var nle:bool;
    var  _0:bool;
    t <- witness;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1) <- CMP_64 x y;
    of_0 <- aux_5;
    _cf_ <- aux_4;
    _sf_ <- aux_3;
     _0 <- aux_2;
    _zf_ <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (_EQ of_0 _cf_ _sf_ _zf_);
    e <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (_uLT of_0 _cf_ _sf_ _zf_);
    b <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (_uLE of_0 _cf_ _sf_ _zf_);
    be <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (_sLT of_0 _cf_ _sf_ _zf_);
    l <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (_sGT of_0 _cf_ _sf_ _zf_);
    nle <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (e ? t.[0] : r);
    r <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- (b ? t.[1] : r);
    r <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (be ? t.[2] : r);
    r <- aux_0;
    leakages <- LeakAddr([3]) :: leakages;
    aux_0 <- ((! be) ? t.[3] : r);
    r <- aux_0;
    leakages <- LeakAddr([4]) :: leakages;
    aux_0 <- (l ? t.[4] : r);
    r <- aux_0;
    leakages <- LeakAddr([5]) :: leakages;
    aux_0 <- ((! l) ? t.[5] : r);
    r <- aux_0;
    leakages <- LeakAddr([6]) :: leakages;
    aux_0 <- ((l \/ e) ? t.[6] : r);
    r <- aux_0;
    leakages <- LeakAddr([7]) :: leakages;
    aux_0 <- (nle ? t.[7] : r);
    r <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (of_0 ? t.[0] : r);
    r <- aux_0;
    return (r);
  }
}.

