require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc strb (arg0:W32.t, arg1:W32.t) : unit = {
    
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRB (truncateu8 arg0));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 2))) (STRB (truncateu8 arg0));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + arg1)) (STRB (truncateu8 arg0));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 1)))) (STRB (truncateu8 arg0));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (STRB (truncateu8 arg0));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 4)))) (STRB (truncateu8 arg0));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 8)))) (STRB (truncateu8 arg0));
    (n, z, c, v) <- CMP arg0 (W32.of_int 0);
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) z (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (! z) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) c (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (! c) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) n (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (! n) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) v (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (! v) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (c /\ (! z)) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) ((! c) \/ z) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (n = v) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (! (n = v)) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) ((! z) /\ (n = v)) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRBcc (truncateu8 arg0) (z \/ (! (n = v))) (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + arg1)) (STRBcc (truncateu8 arg0) z (loadW8 Glob.mem (W32.to_uint (arg0 + arg1))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3))) (STRBcc (truncateu8 arg0) z (loadW8 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3)))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3)))) (STRBcc (truncateu8 arg0) z (loadW8 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3))))));
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (STRBcc (truncateu8 arg0) z (loadW8 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2))))));
    return ();
  }
}.

