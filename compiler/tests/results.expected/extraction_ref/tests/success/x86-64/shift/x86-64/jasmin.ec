require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.

abbrev g = Array1.of_list witness [W64.of_int 6009882477281497451].


module M = {
  proc test_shld (p:W64.t) : unit = {
    
    var a:W16.t;
    var b:W16.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var n:W8.t;
    var c:W32.t;
    var d:W32.t;
    var e:W64.t;
    var f:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    
    a <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 2))));
    (_of_, _cf_, _sf_,  _0, _zf_, a) <- SHLD_16 a b (W8.of_int 3);
    n <- (truncateu8 a);
    n <- (n `&` (W8.of_int 15));
    (_of_, _cf_, _sf_,  _1, _zf_, a) <- SHLD_16 a b n;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (a);
    c <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    d <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))));
    (_of_, _cf_, _sf_,  _2, _zf_, c) <- SHLD_32 c d (W8.of_int 17);
    n <- (W8.of_int 9);
    (_of_, _cf_, _sf_,  _3, _zf_, c) <- SHLD_32 c d n;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (c);
    e <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    f <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))));
    (_of_, _cf_, _sf_,  _4, _zf_, f) <- SHLD_64 f e (W8.of_int 17);
    n <- (W8.of_int 11);
    (_of_, _cf_, _sf_,  _5, _zf_, f) <- SHLD_64 f e n;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (f);
    return ();
  }
  
  proc test_shrd (p:W64.t) : unit = {
    
    var a:W16.t;
    var b:W16.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var n:W8.t;
    var c:W32.t;
    var d:W32.t;
    var e:W64.t;
    var f:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    
    a <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 2))));
    (_of_, _cf_, _sf_,  _0, _zf_, a) <- SHRD_16 a b (W8.of_int 3);
    n <- (truncateu8 a);
    n <- (n `&` (W8.of_int 15));
    (_of_, _cf_, _sf_,  _1, _zf_, a) <- SHRD_16 a b n;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (a);
    c <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    d <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))));
    (_of_, _cf_, _sf_,  _2, _zf_, c) <- SHRD_32 c d (W8.of_int 17);
    n <- (W8.of_int 9);
    (_of_, _cf_, _sf_,  _3, _zf_, c) <- SHRD_32 c d n;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (c);
    e <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    f <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))));
    (_of_, _cf_, _sf_,  _4, _zf_, f) <- SHRD_64 f e (W8.of_int 17);
    n <- (W8.of_int 11);
    (_of_, _cf_, _sf_,  _5, _zf_, f) <- SHRD_64 f e n;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (f);
    return ();
  }
  
  proc test_rorx (x:W64.t) : W32.t = {
    
    var y:W32.t;
    
    x <- RORX_64 x (W8.of_int 0);
    x <- RORX_64 x (W8.of_int 1);
    x <- RORX_64 x (W8.of_int (- 193));
    y <- RORX_32 (truncateu32 x) (W8.of_int 1);
    y <- RORX_32 y (W8.of_int 17);
    return (y);
  }
  
  proc test_bmi_shifts (x:W64.t) : W32.t = {
    
    var z:W32.t;
    var y:W64.t;
    
    y <- x;
    x <- SARX_64 g.[0] x;
    x <- SHRX_64 y x;
    x <- SHLX_64 x x;
    z <- SARX_32 (get32 (WArray8.init64 (fun i => (g).[i])) 0) (truncateu32 x);
    z <- SHRX_32 z (truncateu32 x);
    z <- SHLX_32 (truncateu32 x) z;
    return (z);
  }
}.

