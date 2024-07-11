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
    z <- PCLMULQDQ x y (W8.of_int 16);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (z);
    x <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    y <- x;
    z <- VPCLMULQDQ_128 x y (W8.of_int 17);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (x);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (y);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (z);
    xx <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    yy <- xx;
    zz <- VPCLMULQDQ_256 xx yy (W8.of_int 1);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (xx);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (yy);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (zz);
    return ();
  }
}.

