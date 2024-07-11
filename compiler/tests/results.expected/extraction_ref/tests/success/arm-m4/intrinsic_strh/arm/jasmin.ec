require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc strh (arg0:W32.t, arg1:W32.t) : unit = {
    
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRH (truncateu16 arg0));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 2))) (STRH (truncateu16 arg0));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + arg1)) (STRH (truncateu16 arg0));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 1)))) (STRH (truncateu16 arg0));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (STRH (truncateu16 arg0));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 4)))) (STRH (truncateu16 arg0));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 8)))) (STRH (truncateu16 arg0));
    (n, z, c, v) <- CMP arg0 (W32.of_int 0);
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (! z) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) c (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (! c) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) n (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (! n) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) v (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (! v) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (c /\ (! z)) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) ((! c) \/ z) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (n = v) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (! (n = v)) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) ((! z) /\ (n = v)) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRHcc (truncateu16 arg0) (z \/ (! (n = v))) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + arg1)) (STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + arg1))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3))) (STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3)))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3)))) (STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3))))));
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2))))));
    return ();
  }
}.

