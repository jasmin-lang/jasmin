require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc strb (arg:W32.t) : unit = {
    
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- arg;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg + (W32.of_int 0))) ((truncateu8 x));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 3))) ((truncateu8 x));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))) ((truncateu8 x));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))) ((truncateu8 x));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) ((truncateu8 x));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))) ((truncateu8 x));
    (n, z, c, v) <- CMP x (W32.of_int 0);
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((z ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((c ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! c) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((n ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! n) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((v ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! v) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((c /\ (! z)) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((((! c) \/ z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((n = v) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! (n = v)) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((((! z) /\ (n = v)) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((z \/ (! (n = v))) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + arg)) (((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + arg)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 3))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))))));
    return ();
  }
}.

