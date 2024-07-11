require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_ptest (rp:W64.t) : unit = {
    
    var r:W64.t;
    var f:W64.t;
    var g:W256.t;
    var zf:bool;
    var h:W128.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    
    r <- (W64.of_int 1);
    f <- (W64.of_int 0);
    g <- set0_256 ;
    ( _0,  _1,  _2,  _3, zf) <- VPTEST_256 g g;
    r <- ((! zf) ? f : r);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (r);
    h <- set0_128 ;
    ( _4,  _5,  _6,  _7, zf) <- VPTEST_128 h h;
    r <- ((! zf) ? f : r);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (r);
    return ();
  }
}.

