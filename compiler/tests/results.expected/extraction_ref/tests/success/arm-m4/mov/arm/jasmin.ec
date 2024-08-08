require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc mov (arg0:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- arg0;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (W32.of_int 3402287818);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (W32.of_int 3389049344);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (W32.of_int 13238474);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (W32.of_int 51968);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (W32.of_int 51914);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (n, z, c, v) <- CMP x (W32.of_int 0);
    x <- (z ? arg0 : x);
    x <- ((! z) ? arg0 : x);
    x <- (c ? arg0 : x);
    x <- ((! c) ? arg0 : x);
    x <- (n ? arg0 : x);
    x <- ((! n) ? arg0 : x);
    x <- (v ? arg0 : x);
    x <- ((! v) ? arg0 : x);
    x <- ((c /\ (! z)) ? arg0 : x);
    x <- (((! c) \/ z) ? arg0 : x);
    x <- ((n = v) ? arg0 : x);
    x <- ((! (n = v)) ? arg0 : x);
    x <- (((! z) /\ (n = v)) ? arg0 : x);
    x <- ((z \/ (! (n = v))) ? arg0 : x);
    x <- (c ? (W32.of_int 1) : x);
    x <- (c ? (W32.of_int 3402287818) : x);
    x <- (c ? (W32.of_int 3389049344) : x);
    x <- (c ? (W32.of_int 13238474) : x);
    x <- (c ? (W32.of_int 51968) : x);
    x <- (c ? (W32.of_int 51914) : x);
    res_0 <- x;
    return (res_0);
  }
}.

