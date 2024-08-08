require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc add (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    
    x <- ADD arg0 arg1;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (W32.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (W32.of_int (- 1));
    x <- ADD x (W32.of_int 3402287818);
    x <- ADD x (W32.of_int 3389049344);
    x <- ADD x (W32.of_int 13238474);
    x <- ADD x (W32.of_int 831488);
    x <- ADD x (W32.of_int 2762);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `<<` (W8.of_int 0));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `<<` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `<<` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `|>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `|>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `|>>|` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ADD arg0 (arg1 `|>>|` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, vf, x) <- ADDS x arg0;
    x <- ADDcc arg0 arg1 zf x;
    x <- ADDcc arg0 arg1 (! zf) x;
    x <- ADDcc arg0 arg1 cf x;
    x <- ADDcc arg0 arg1 (! cf) x;
    x <- ADDcc arg0 arg1 nf x;
    x <- ADDcc arg0 arg1 (! nf) x;
    x <- ADDcc arg0 arg1 vf x;
    x <- ADDcc arg0 arg1 (! vf) x;
    x <- ADDcc arg0 arg1 (cf /\ (! zf)) x;
    x <- ADDcc arg0 arg1 ((! cf) \/ zf) x;
    x <- ADDcc arg0 arg1 (nf = vf) x;
    x <- ADDcc arg0 arg1 (! (nf = vf)) x;
    x <- ADDcc arg0 arg1 ((! zf) /\ (nf = vf)) x;
    x <- ADDcc arg0 arg1 (zf \/ (! (nf = vf))) x;
    (nf, zf, cf, vf, x) <- ADDScc x arg0 (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- ADDS x (W32.of_int 2);
    (_nf_, _zf_, _cf_, _vf_, x) <- ADDS x (W32.of_int 3402287818);
    (_nf_, _zf_, _cf_, _vf_, x) <- ADDS x (W32.of_int 3389049344);
    (_nf_, _zf_, _cf_, _vf_, x) <- ADDS x (W32.of_int 13238474);
    (_nf_, _zf_, _cf_, _vf_, x) <- ADDS x (W32.of_int 13303808);
    (nf, zf, cf, vf, x) <- ADDS x (arg0 `<<` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- ADDS x (arg0 `>>` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- ADDS x (arg0 `|>>` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- ADDS x (arg0 `|>>|` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- ADDScc x (W32.of_int 2) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- ADDScc x (arg0 `<<` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- ADDScc x (arg0 `<<` (W8.of_int 3)) (! (! (nf = vf))) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- ADDScc x (arg0 `>>` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- ADDScc x (arg0 `|>>` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- ADDScc x (arg0 `|>>|` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    x <- ADDcc x arg0 (! (! (! (! zf)))) x;
    x <- ADDcc x (W32.of_int 2) zf x;
    x <- ADDcc x (W32.of_int 2) (! (! zf)) x;
    x <- ADDcc x (arg0 `<<` (W8.of_int 3)) zf x;
    x <- ADDcc x (arg0 `<<` (W8.of_int 3)) (! (! zf)) x;
    x <- ADDcc x (arg0 `>>` (W8.of_int 3)) zf x;
    x <- ADDcc x (arg0 `|>>` (W8.of_int 3)) zf x;
    x <- ADDcc x (arg0 `|>>|` (W8.of_int 3)) zf x;
    res_0 <- x;
    return (res_0);
  }
}.

