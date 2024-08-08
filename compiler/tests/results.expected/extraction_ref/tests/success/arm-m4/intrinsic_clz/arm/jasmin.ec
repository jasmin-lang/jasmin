require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc main (x:W32.t) : W32.t = {
    
    var y:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var b:bool;
    
    y <- CLZ x;
    (_nf_, _zf_, _cf_, _vf_) <- CMP y (W32.of_int 9);
    b <- (_sLT _nf_ _zf_ _cf_ _vf_);
    y <- CLZcc y b y;
    return (y);
  }
}.

