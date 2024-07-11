require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc threeway (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var below:bool;
    var equal:bool;
    var  _0:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_) <- CMP_64 x (W64.of_int 2);
    below <- (_uLT _of_ _cf_ _sf_ _zf_);
    equal <- (_EQ _of_ _cf_ _sf_ _zf_);
    if (below) {
      r <- (W64.of_int 1);
    } else {
      if (equal) {
        r <- (W64.of_int 2);
      } else {
        r <- (W64.of_int 3);
      }
    }
    return (r);
  }
}.

