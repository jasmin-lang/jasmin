require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (a:W64.t, b:W64.t) : W64.t = {
    
    var res_0:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cond:bool;
    var one:W64.t;
    var  _0:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_) <- CMP_64 a b;
    cond <- (_NEQ _of_ _cf_ _sf_ _zf_);
    res_0 <- (W64.of_int 0);
    one <- (W64.of_int 1);
    res_0 <- (cond ? one : res_0);
    return (res_0);
  }
}.

