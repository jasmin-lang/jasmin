require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc smul_hw (x:W32.t, y:W32.t) : W32.t = {
    
    var r:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var b:bool;
    
    r <- SMULBB x y;
    r <- SMULBT r y;
    r <- SMULTB r y;
    r <- SMULTT r y;
    (_nf_, _zf_, _cf_, _vf_) <- CMP r y;
    b <- (_sLT _nf_ _zf_ _cf_ _vf_);
    r <- SMULBBcc r y b r;
    r <- SMULBTcc r y b r;
    r <- SMULTBcc r y b r;
    r <- SMULTTcc r y b r;
    return (r);
  }
}.

