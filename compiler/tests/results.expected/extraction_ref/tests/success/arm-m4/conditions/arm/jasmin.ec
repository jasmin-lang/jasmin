require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc test_conditions (x:W32.t, y:W32.t) : W32.t = {
    
    var r:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var eq:bool;
    var neq:bool;
    
    (_nf_, _zf_, _cf_, _vf_) <- CMP x y;
    eq <- (_EQ _nf_ _zf_ _cf_ _vf_);
    neq <- (_NEQ _nf_ _zf_ _cf_ _vf_);
    r <- (W32.of_int 0);
    r <- (eq ? x : r);
    r <- (neq ? y : r);
    r <- r;
    return (r);
  }
}.

