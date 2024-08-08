require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array8.
require import WArray32.



module M = {
  proc test_cmp (x:W32.t, y:W32.t) : W32.t = {
    var aux: int;
    
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
    i <- 0;
    while (i < 8) {
      t.[i] <- (W32.of_int i);
      i <- i + 1;
    }
    (_nf_, _zf_, _cf_, vf) <- CMP x y;
    e <- (_EQ _nf_ _zf_ _cf_ vf);
    b <- (_uLT _nf_ _zf_ _cf_ vf);
    be <- (_uLE _nf_ _zf_ _cf_ vf);
    l <- (_sLT _nf_ _zf_ _cf_ vf);
    nle <- (_sGT _nf_ _zf_ _cf_ vf);
    r <- (W32.of_int 0);
    r <- (e ? t.[0] : r);
    r <- (b ? t.[1] : r);
    r <- (be ? t.[2] : r);
    r <- ((! be) ? t.[3] : r);
    r <- (l ? t.[4] : r);
    r <- ((! l) ? t.[5] : r);
    r <- ((l \/ e) ? t.[6] : r);
    r <- (nle ? t.[7] : r);
    r <- (vf ? t.[0] : r);
    return (r);
  }
}.

