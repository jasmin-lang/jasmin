require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc cond_swap (p:W32.t, q:W32.t, cond:W32.t) : unit = {
    
    var f:bool;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var d:W32.t;
    
    f <- (cond <> (W32.of_int 0));
    a <- (loadW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))));
    b <- (loadW32 Glob.mem (W32.to_uint (q + (W32.of_int 0))));
    c <- (f ? b : c);
    d <- (f ? a : d);
    c <- ((! f) ? a : c);
    d <- ((! f) ? b : d);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))) (c);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (q + (W32.of_int 0))) (d);
    return ();
  }
}.

