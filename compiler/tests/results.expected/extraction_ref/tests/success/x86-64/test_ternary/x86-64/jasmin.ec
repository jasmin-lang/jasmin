require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array8.
require import WArray64.



module M = {
  proc test_cmp (x:W64.t, y:W64.t) : W64.t = {
    var aux: int;
    
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
    i <- 0;
    while (i < 8) {
      t.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    (of_0, _cf_, _sf_,  _0, _zf_) <- CMP_64 x y;
    e <- (_EQ of_0 _cf_ _sf_ _zf_);
    b <- (_uLT of_0 _cf_ _sf_ _zf_);
    be <- (_uLE of_0 _cf_ _sf_ _zf_);
    l <- (_sLT of_0 _cf_ _sf_ _zf_);
    nle <- (_sGT of_0 _cf_ _sf_ _zf_);
    r <- (W64.of_int 0);
    r <- (e ? t.[0] : r);
    r <- (b ? t.[1] : r);
    r <- (be ? t.[2] : r);
    r <- ((! be) ? t.[3] : r);
    r <- (l ? t.[4] : r);
    r <- ((! l) ? t.[5] : r);
    r <- ((l \/ e) ? t.[6] : r);
    r <- (nle ? t.[7] : r);
    r <- (of_0 ? t.[0] : r);
    return (r);
  }
}.

