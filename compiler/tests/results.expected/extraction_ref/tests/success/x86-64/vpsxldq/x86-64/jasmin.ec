require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W256.t;
    var e:W256.t;
    var f:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VPSLLDQ_128 a (W8.of_int 1);
    c <- VPSRLDQ_128 b (W8.of_int 2);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))) (c);
    d <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    e <- VPSLLDQ_256 d (W8.of_int 3);
    f <- VPSRLDQ_256 e (W8.of_int 4);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (f);
    return ();
  }
}.

