require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (b:W8.t, x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    var c:bool;
    
    r <- x;
    c <- (b = (W8.of_int 1));
    r <- (c ? y : r);
    c <- (x \slt y);
    r <- (c ? y : r);
    c <- (x \ult y);
    r <- (c ? y : r);
    c <- (x \sle y);
    r <- (c ? y : r);
    c <- (x \ule y);
    r <- (c ? y : r);
    c <- (x = y);
    r <- (c ? y : r);
    c <- (y \ule x);
    r <- (c ? y : r);
    c <- (y \sle x);
    r <- (c ? y : r);
    c <- (y \ult x);
    r <- (c ? y : r);
    c <- (y \slt x);
    r <- (c ? y : r);
    return (r);
  }
  
  proc g (x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    var of_0:bool;
    var cf:bool;
    var sf:bool;
    var zf:bool;
    var b0:bool;
    var c:bool;
    var b1:bool;
    var b2:bool;
    var z:W8.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    var  _1:bool;
    
    (of_0, cf, sf,  _0, zf) <- CMP_64 x y;
    b0 <- (_EQ of_0 cf sf zf);
    c <- (_sLT of_0 cf sf zf);
    b1 <- (_uLT of_0 cf sf zf);
    b2 <- (_uGT of_0 cf sf zf);
    r <- (b0 ? y : r);
    r <- (b1 ? y : r);
    z <- SETcc b1;
    x <- (zeroextu64 z);
    r <- (b2 ? y : r);
    r <- (r + x);
    (_of_, _cf_, _sf_,  _1, _zf_) <- CMP_64 x y;
    b0 <- (_EQ _of_ _cf_ _sf_ _zf_);
    c <- (_sLT _of_ _cf_ _sf_ _zf_);
    b1 <- (_uLT _of_ _cf_ _sf_ _zf_);
    r <- (b0 ? y : r);
    r <- (b1 ? y : r);
    z <- SETcc b1;
    x <- (zeroextu64 z);
    r <- (r + x);
    return (r);
  }
}.

