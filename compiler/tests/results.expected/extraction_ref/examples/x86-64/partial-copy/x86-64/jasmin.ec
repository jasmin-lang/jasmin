require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array17.
require import WArray68.



module M = {
  proc use (t:W32.t Array17.t) : W32.t = {
    var aux: int;
    
    var s:W32.t;
    var i:int;
    
    s <- (W32.of_int 0);
    i <- 0;
    while (i < 17) {
      s <- (s + t.[i]);
      i <- i + 1;
    }
    return (s);
  }
  
  proc copy (in_0:W64.t, inlen:W64.t) : W32.t = {
    var aux: int;
    
    var r:W32.t;
    var one:W32.t;
    var size:W8.t;
    var tmp:W32.t;
    var i:int;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var eq:bool;
    var le:bool;
    var t:W32.t Array17.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    t <- witness;
    one <- (W32.of_int 1);
    
    while (((W64.of_int 0) \slt inlen)) {
      size <- (truncateu8 inlen);
      size <- (size `&` (W8.of_int 15));
      i <- 0;
      while (i < 17) {
        ( _0,  _1,  _2,  _3,  _4, tmp) <- set0_32 ;
        (_of_, _cf_, _sf_,  _5, _zf_) <- CMP_8 size (W8.of_int i);
        eq <- (_EQ _of_ _cf_ _sf_ _zf_);
        le <- (_sLE _of_ _cf_ _sf_ _zf_);
        tmp <- ((! le) ? (loadW32 Glob.mem (W64.to_uint (in_0 + (W64.of_int i)))) : tmp);
        tmp <- (eq ? one : tmp);
        t.[i] <- tmp;
        i <- i + 1;
      }
      in_0 <- (in_0 + (W64.of_int 16));
      inlen <- (inlen - (W64.of_int 16));
    }
    r <@ use (t);
    return (r);
  }
}.

