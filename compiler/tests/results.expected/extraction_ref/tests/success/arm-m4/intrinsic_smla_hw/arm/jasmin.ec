require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc smla_hw (x:W32.t, y:W32.t, acc:W32.t) : W32.t = {
    
    var r:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var b:bool;
    
    r <- SMLABB x y acc;
    r <- SMLABT x y r;
    r <- SMLATB x y r;
    r <- SMLATT x y r;
    (_nf_, _zf_, _cf_, _vf_) <- CMP x y;
    b <- (_sLT _nf_ _zf_ _cf_ _vf_);
    r <- SMLABBcc x y r b r;
    r <- SMLABTcc x y r b r;
    r <- SMLATBcc x y r b r;
    r <- SMLATTcc x y r b r;
    r <- r;
    return (r);
  }
}.

