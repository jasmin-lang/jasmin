require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array8.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc test_cmp (x:W32.t, y:W32.t) : W32.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W32.t;
    
    var r:W32.t;
    var i:int;
    var t:W32.t Array8.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var vf:bool;
    var e:bool;
    var b:bool;
    var be:bool;
    var l:bool;
    var nle:bool;
    t <- witness;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W32.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1) <- CMP x y;
    _nf_ <- aux_4;
    _zf_ <- aux_3;
    _cf_ <- aux_2;
    vf <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (_EQ _nf_ _zf_ _cf_ vf);
    e <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (_uLT _nf_ _zf_ _cf_ vf);
    b <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (_uLE _nf_ _zf_ _cf_ vf);
    be <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (_sLT _nf_ _zf_ _cf_ vf);
    l <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (_sGT _nf_ _zf_ _cf_ vf);
    nle <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
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
    aux_0 <- (vf ? t.[0] : r);
    r <- aux_0;
    return (r);
  }
}.

