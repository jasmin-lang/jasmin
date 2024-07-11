require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc strh (arg:W32.t) : unit = {
    
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- arg;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg + (W32.of_int 0))) ((truncateu16 x));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 3))) ((truncateu16 x));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))) ((truncateu16 x));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))) ((truncateu16 x));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) ((truncateu16 x));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))) ((truncateu16 x));
    (n, z, c, v) <- CMP x (W32.of_int 0);
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((z ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((c ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! c) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((n ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! n) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((v ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! v) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((c /\ (! z)) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((((! c) \/ z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((n = v) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! (n = v)) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((((! z) /\ (n = v)) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((z \/ (! (n = v))) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + arg)) (((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + arg)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 3))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))))));
    return ();
  }
}.

