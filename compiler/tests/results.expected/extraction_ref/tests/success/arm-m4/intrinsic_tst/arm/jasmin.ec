require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc tst (arg0:W32.t, arg1:W32.t, p:W32.t) : unit = {
    
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- (W32.of_int 0);
    (n, z, c) <- TST arg0 arg1;
    x <- (n ? (W32.of_int 1) : x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))) (x);
    (n, z, c) <- TST arg0 (W32.of_int 3);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    (n, z, c) <- TST x (W32.of_int 3402287818);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    (n, z, c) <- TST x (W32.of_int 3389049344);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    (n, z, c) <- TST x (W32.of_int 13238474);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) ((z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))))));
    (n, z, c, v) <- CMP arg0 (W32.of_int 0);
    (n, z, c) <- TSTcc arg0 arg1 z n z c;
    (n, z, c) <- TSTcc arg0 arg1 (! z) n z c;
    (n, z, c) <- TSTcc arg0 arg1 c n z c;
    (n, z, c) <- TSTcc arg0 arg1 (! c) n z c;
    (n, z, c) <- TSTcc arg0 arg1 n n z c;
    (n, z, c) <- TSTcc arg0 arg1 (! n) n z c;
    (n, z, c) <- TSTcc arg0 arg1 v n z c;
    (n, z, c) <- TSTcc arg0 arg1 (! v) n z c;
    (n, z, c) <- TSTcc arg0 arg1 (c /\ (! z)) n z c;
    (n, z, c) <- TSTcc arg0 arg1 ((! c) \/ z) n z c;
    (n, z, c) <- TSTcc arg0 arg1 (n = v) n z c;
    (n, z, c) <- TSTcc arg0 arg1 (! (n = v)) n z c;
    (n, z, c) <- TSTcc arg0 arg1 ((! z) /\ (n = v)) n z c;
    (n, z, c) <- TSTcc arg0 arg1 (z \/ (! (n = v))) n z c;
    (n, z, c) <- TSTcc arg0 (W32.of_int 3) z n z c;
    x <- (n ? (W32.of_int 1) : x);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))) (x);
    return ();
  }
}.

