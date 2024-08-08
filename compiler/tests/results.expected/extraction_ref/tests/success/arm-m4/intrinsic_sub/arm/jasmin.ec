require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc sub (arg0:W32.t, arg1:W32.t) : W32.t = {
    
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
    
    x <- SUB arg0 arg1;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (W32.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (W32.of_int (- 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB x (W32.of_int 3402287818);
    x <- SUB x (W32.of_int 3389049344);
    x <- SUB x (W32.of_int 13238474);
    x <- SUB x (W32.of_int 831488);
    x <- SUB x (W32.of_int 2762);
    x <- SUB arg0 (arg1 `<<` (W8.of_int 0));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `<<` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `<<` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `|>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `|>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `|>>|` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- SUB arg0 (arg1 `|>>|` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, vf, x) <- SUBS x arg0;
    x <- SUBcc arg0 arg1 zf x;
    x <- SUBcc arg0 arg1 (! zf) x;
    x <- SUBcc arg0 arg1 cf x;
    x <- SUBcc arg0 arg1 (! cf) x;
    x <- SUBcc arg0 arg1 nf x;
    x <- SUBcc arg0 arg1 (! nf) x;
    x <- SUBcc arg0 arg1 vf x;
    x <- SUBcc arg0 arg1 (! vf) x;
    x <- SUBcc arg0 arg1 (cf /\ (! zf)) x;
    x <- SUBcc arg0 arg1 ((! cf) \/ zf) x;
    x <- SUBcc arg0 arg1 (nf = vf) x;
    x <- SUBcc arg0 arg1 (! (nf = vf)) x;
    x <- SUBcc arg0 arg1 ((! zf) /\ (nf = vf)) x;
    x <- SUBcc arg0 arg1 (zf \/ (! (nf = vf))) x;
    (nf, zf, cf, vf, x) <- SUBScc x arg0 (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- SUBS x (W32.of_int 2);
    (_nf_, _zf_, _cf_, _vf_, x) <- SUBS x (W32.of_int 3402287818);
    (_nf_, _zf_, _cf_, _vf_, x) <- SUBS x (W32.of_int 3389049344);
    (_nf_, _zf_, _cf_, _vf_, x) <- SUBS x (W32.of_int 13238474);
    (_nf_, _zf_, _cf_, _vf_, x) <- SUBS x (W32.of_int 13303808);
    (nf, zf, cf, vf, x) <- SUBS x (arg0 `<<` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- SUBS x (arg0 `>>` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- SUBS x (arg0 `|>>` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- SUBS x (arg0 `|>>|` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- SUBScc x (W32.of_int 2) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- SUBScc x (arg0 `<<` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- SUBScc x (arg0 `<<` (W8.of_int 3)) (! (! (nf = vf))) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- SUBScc x (arg0 `>>` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- SUBScc x (arg0 `|>>` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- SUBScc x (arg0 `|>>|` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    x <- SUBcc x arg0 (! (! (! (! zf)))) x;
    x <- SUBcc x (W32.of_int 2) zf x;
    x <- SUBcc x (W32.of_int 2) (! (! zf)) x;
    x <- SUBcc x (arg0 `<<` (W8.of_int 3)) zf x;
    x <- SUBcc x (arg0 `<<` (W8.of_int 3)) (! (! zf)) x;
    x <- SUBcc x (arg0 `>>` (W8.of_int 3)) zf x;
    x <- SUBcc x (arg0 `|>>` (W8.of_int 3)) zf x;
    x <- SUBcc x (arg0 `|>>|` (W8.of_int 3)) zf x;
    res_0 <- x;
    return (res_0);
  }
}.

