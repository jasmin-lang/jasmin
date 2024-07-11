require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (in_0:W64.t) : unit = {
    
    var x:W128.t;
    var y:W128.t;
    var z:W128.t;
    var xx:W256.t;
    var yy:W256.t;
    var zz:W256.t;
    
    x <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    y <- x;
    z <- VPBLEND_8u16 x y (W8.of_int 237);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (z);
    x <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    y <- x;
    z <- VPBLEND_4u32 x y (W8.of_int 237);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (z);
    xx <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    yy <- xx;
    zz <- VPBLEND_16u16 xx yy (W8.of_int 237);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (zz);
    xx <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    yy <- xx;
    zz <- VPBLEND_8u32 xx yy (W8.of_int 237);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (zz);
    return ();
  }
}.

