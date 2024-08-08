require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc mvn (arg0:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    
    x <- MVN arg0;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (W32.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (W32.of_int (- 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (W32.of_int 3402287818);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (W32.of_int 3389049344);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (W32.of_int 13238474);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `<<` (W8.of_int 0));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `<<` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `<<` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `|>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `|>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `|>>|` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- MVN (arg0 `|>>|` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- MVNS arg0;
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- MVNcc arg0 zf x;
    x <- MVNcc arg0 (! zf) x;
    x <- MVNcc arg0 cf x;
    x <- MVNcc arg0 (! cf) x;
    x <- MVNcc arg0 nf x;
    x <- MVNcc arg0 (! nf) x;
    x <- MVNcc arg0 vf x;
    x <- MVNcc arg0 (! vf) x;
    x <- MVNcc arg0 (cf /\ (! zf)) x;
    x <- MVNcc arg0 ((! cf) \/ zf) x;
    x <- MVNcc arg0 (nf = vf) x;
    x <- MVNcc arg0 (! (nf = vf)) x;
    x <- MVNcc arg0 ((! zf) /\ (nf = vf)) x;
    x <- MVNcc arg0 (zf \/ (! (nf = vf))) x;
    (nf, zf, cf, x) <- MVNScc arg0 (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- MVNS (W32.of_int 2);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (_nf_, _zf_, _cf_, x) <- MVNS (W32.of_int 3402287818);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (_nf_, _zf_, _cf_, x) <- MVNS (W32.of_int 3389049344);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (_nf_, _zf_, _cf_, x) <- MVNS (W32.of_int 13238474);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- MVNS (arg0 `<<` (W8.of_int 3));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- MVNS (arg0 `>>` (W8.of_int 3));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- MVNS (arg0 `|>>` (W8.of_int 3));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- MVNS (arg0 `|>>|` (W8.of_int 3));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- MVNScc (W32.of_int 2) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- MVNScc (arg0 `<<` (W8.of_int 3)) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- MVNScc (arg0 `<<` (W8.of_int 3)) (! (! (nf = vf))) nf zf cf x;
    (nf, zf, cf, x) <- MVNScc (arg0 `>>` (W8.of_int 3)) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- MVNScc (arg0 `|>>` (W8.of_int 3)) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- MVNScc (arg0 `|>>|` (W8.of_int 3)) (nf = vf) nf zf cf x;
    x <- MVNcc arg0 (! (! (! (! zf)))) x;
    x <- MVNcc (W32.of_int 2) zf x;
    x <- MVNcc (W32.of_int 2) (! (! zf)) x;
    x <- MVNcc (arg0 `<<` (W8.of_int 3)) zf x;
    x <- MVNcc (arg0 `<<` (W8.of_int 3)) (! (! zf)) x;
    x <- MVNcc (arg0 `>>` (W8.of_int 3)) zf x;
    x <- MVNcc (arg0 `|>>` (W8.of_int 3)) zf x;
    x <- MVNcc (arg0 `|>>|` (W8.of_int 3)) zf x;
    res_0 <- x;
    return (res_0);
  }
}.

