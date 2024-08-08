require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc orr (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    
    x <- ORR arg0 arg1;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (W32.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (W32.of_int (- 1));
    x <- ORR x (W32.of_int 3402287818);
    x <- ORR x (W32.of_int 3389049344);
    x <- ORR x (W32.of_int 13238474);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `<<` (W8.of_int 0));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `<<` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `<<` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `|>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `|>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `|>>|` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- ORR arg0 (arg1 `|>>|` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- ORRS x arg0;
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- ORRcc arg0 arg1 zf x;
    x <- ORRcc arg0 arg1 (! zf) x;
    x <- ORRcc arg0 arg1 cf x;
    x <- ORRcc arg0 arg1 (! cf) x;
    x <- ORRcc arg0 arg1 nf x;
    x <- ORRcc arg0 arg1 (! nf) x;
    x <- ORRcc arg0 arg1 vf x;
    x <- ORRcc arg0 arg1 (! vf) x;
    x <- ORRcc arg0 arg1 (cf /\ (! zf)) x;
    x <- ORRcc arg0 arg1 ((! cf) \/ zf) x;
    x <- ORRcc arg0 arg1 (nf = vf) x;
    x <- ORRcc arg0 arg1 (! (nf = vf)) x;
    x <- ORRcc arg0 arg1 ((! zf) /\ (nf = vf)) x;
    x <- ORRcc arg0 arg1 (zf \/ (! (nf = vf))) x;
    (nf, zf, cf, x) <- ORRScc x arg0 (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- ORRS x (W32.of_int 2);
    (_nf_, _zf_, _cf_, x) <- ORRS x (W32.of_int 3402287818);
    (_nf_, _zf_, _cf_, x) <- ORRS x (W32.of_int 3389049344);
    (_nf_, _zf_, _cf_, x) <- ORRS x (W32.of_int 13238474);
    (nf, zf, cf, x) <- ORRS x (arg0 `<<` (W8.of_int 3));
    (nf, zf, cf, x) <- ORRS x (arg0 `>>` (W8.of_int 3));
    (nf, zf, cf, x) <- ORRS x (arg0 `|>>` (W8.of_int 3));
    (nf, zf, cf, x) <- ORRS x (arg0 `|>>|` (W8.of_int 3));
    (nf, zf, cf, x) <- ORRScc x (W32.of_int 2) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- ORRScc x (arg0 `<<` (W8.of_int 3)) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- ORRScc x (arg0 `<<` (W8.of_int 3)) (! (! (nf = vf))) nf zf cf x;
    (nf, zf, cf, x) <- ORRScc x (arg0 `>>` (W8.of_int 3)) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- ORRScc x (arg0 `|>>` (W8.of_int 3)) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- ORRScc x (arg0 `|>>|` (W8.of_int 3)) (nf = vf) nf zf cf x;
    x <- ORRcc x arg0 (! (! (! (! zf)))) x;
    x <- ORRcc x (W32.of_int 2) zf x;
    x <- ORRcc x (W32.of_int 2) (! (! zf)) x;
    x <- ORRcc x (arg0 `<<` (W8.of_int 3)) zf x;
    x <- ORRcc x (arg0 `<<` (W8.of_int 3)) (! (! zf)) x;
    x <- ORRcc x (arg0 `>>` (W8.of_int 3)) zf x;
    x <- ORRcc x (arg0 `|>>` (W8.of_int 3)) zf x;
    x <- ORRcc x (arg0 `|>>|` (W8.of_int 3)) zf x;
    res_0 <- x;
    return (res_0);
  }
}.

