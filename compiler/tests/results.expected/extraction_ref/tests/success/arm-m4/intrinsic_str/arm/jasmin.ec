require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc str (arg0:W32.t, arg1:W32.t) : unit = {
    
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STR arg0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 2))) (STR arg0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + arg1)) (STR arg0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 1)))) (STR arg0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (STR arg0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 4)))) (STR arg0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 8)))) (STR arg0);
    (n, z, c, v) <- CMP arg0 (W32.of_int 0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 z (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (! z) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 c (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (! c) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 n (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (! n) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 v (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (! v) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (c /\ (! z)) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 ((! c) \/ z) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (n = v) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (! (n = v)) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 ((! z) /\ (n = v)) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (STRcc arg0 (z \/ (! (n = v))) (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + arg1)) (STRcc arg0 z (loadW32 Glob.mem (W32.to_uint (arg0 + arg1))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3))) (STRcc arg0 z (loadW32 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3)))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3)))) (STRcc arg0 z (loadW32 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3))))));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (STRcc arg0 z (loadW32 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2))))));
    return ();
  }
}.

