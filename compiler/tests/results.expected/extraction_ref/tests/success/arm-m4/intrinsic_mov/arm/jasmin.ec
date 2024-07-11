require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc mov (arg0:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- arg0;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MOV (W32.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MOV (W32.of_int 3402287818);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MOV (W32.of_int 3389049344);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MOV (W32.of_int 13238474);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MOV (W32.of_int 51968);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MOV (W32.of_int 51914);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (_nf_, _zf_, _cf_, x) <- MOVS x;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (_nf_, _zf_, _cf_, x) <- MOVS (W32.of_int 3402287818);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (_nf_, _zf_, _cf_, x) <- MOVS (W32.of_int 3389049344);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (_nf_, _zf_, _cf_, x) <- MOVS (W32.of_int 13238474);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (n, z, c, v) <- CMP x (W32.of_int 0);
    x <- MOVcc x z x;
    x <- MOVcc x (! z) x;
    x <- MOVcc x c x;
    x <- MOVcc x (! c) x;
    x <- MOVcc x n x;
    x <- MOVcc x (! n) x;
    x <- MOVcc x v x;
    x <- MOVcc x (! v) x;
    x <- MOVcc x (c /\ (! z)) x;
    x <- MOVcc x ((! c) \/ z) x;
    x <- MOVcc x (n = v) x;
    x <- MOVcc x (! (n = v)) x;
    x <- MOVcc x ((! z) /\ (n = v)) x;
    x <- MOVcc x (z \/ (! (n = v))) x;
    x <- MOVcc (W32.of_int 1) (! z) x;
    (n, z, c, x) <- MOVScc arg0 (! z) n z c x;
    (n, z, c, x) <- MOVScc (W32.of_int 49) (! (! z)) n z c x;
    res_0 <- x;
    return (res_0);
  }
}.

