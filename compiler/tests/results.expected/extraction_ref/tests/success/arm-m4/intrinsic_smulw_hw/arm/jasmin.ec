require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc smulw_hw (x:W32.t, y:W32.t) : W32.t = {
    
    var r:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var b:bool;
    
    r <- SMULWB x y;
    r <- SMULWT r y;
    (_nf_, _zf_, _cf_, _vf_) <- CMP r y;
    b <- (_sLT _nf_ _zf_ _cf_ _vf_);
    r <- SMULWBcc r y b r;
    r <- SMULWTcc r y b r;
    r <- r;
    return (r);
  }
}.

