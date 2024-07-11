require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc str (arg:W32.t) : unit = {
    
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- arg;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg + (W32.of_int 0))) (x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))) (x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))) (x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))) (x);
    (n, z, c, v) <- CMP x (W32.of_int 0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((c ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! c) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((n ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! n) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((v ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! v) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((c /\ (! z)) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((((! c) \/ z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((n = v) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((! (n = v)) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((((! z) /\ (n = v)) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (((z \/ (! (n = v))) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + arg)) (((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + arg)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 3))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))))));
    return ();
  }
}.

