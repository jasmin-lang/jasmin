require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc bfc (x:W32.t) : W32.t = {
    
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var b:bool;
    
    x <- BFC x (W8.of_int 0) (W8.of_int 1);
    x <- BFC x (W8.of_int 31) (W8.of_int 1);
    x <- BFC x (W8.of_int 0) (W8.of_int 32);
    (_nf_, _zf_, _cf_, _vf_) <- CMP x (W32.of_int 5);
    b <- (_sLT _nf_ _zf_ _cf_ _vf_);
    x <- BFCcc x (W8.of_int 0) (W8.of_int 32) b x;
    return (x);
  }
}.

