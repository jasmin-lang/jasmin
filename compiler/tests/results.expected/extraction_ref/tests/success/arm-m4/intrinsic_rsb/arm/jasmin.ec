require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc rsb (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- RSB arg0 arg1;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (W32.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (W32.of_int (- 1));
    x <- RSB x (W32.of_int 3402287818);
    x <- RSB x (W32.of_int 3389049344);
    x <- RSB x (W32.of_int 13238474);
    x <- RSB x (W32.of_int 13303808);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `<<` (W8.of_int 0));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `<<` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `<<` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `|>>` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `|>>` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `|>>|` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- RSB arg0 (arg1 `|>>|` (W8.of_int 31));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, vf, x) <- RSBS x arg0;
    x <- RSBcc arg0 arg1 zf x;
    x <- RSBcc arg0 arg1 (! zf) x;
    x <- RSBcc arg0 arg1 cf x;
    x <- RSBcc arg0 arg1 (! cf) x;
    x <- RSBcc arg0 arg1 nf x;
    x <- RSBcc arg0 arg1 (! nf) x;
    x <- RSBcc arg0 arg1 vf x;
    x <- RSBcc arg0 arg1 (! vf) x;
    x <- RSBcc arg0 arg1 (cf /\ (! zf)) x;
    x <- RSBcc arg0 arg1 ((! cf) \/ zf) x;
    x <- RSBcc arg0 arg1 (nf = vf) x;
    x <- RSBcc arg0 arg1 (! (nf = vf)) x;
    x <- RSBcc arg0 arg1 ((! zf) /\ (nf = vf)) x;
    x <- RSBcc arg0 arg1 (zf \/ (! (nf = vf))) x;
    (nf, zf, cf, vf, x) <- RSBScc x arg0 (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- RSBS x (W32.of_int 2);
    (nf, zf, cf, vf, x) <- RSBS x (arg0 `<<` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- RSBS x (arg0 `>>` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- RSBS x (arg0 `|>>` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- RSBS x (arg0 `|>>|` (W8.of_int 3));
    (nf, zf, cf, vf, x) <- RSBScc x (W32.of_int 2) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- RSBScc x (arg0 `<<` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- RSBScc x (arg0 `<<` (W8.of_int 3)) (! (! (nf = vf))) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- RSBScc x (arg0 `>>` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- RSBScc x (arg0 `|>>` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    (nf, zf, cf, vf, x) <- RSBScc x (arg0 `|>>|` (W8.of_int 3)) (nf = vf) nf zf cf vf x;
    x <- RSBcc x arg0 (! (! (! (! zf)))) x;
    x <- RSBcc x (W32.of_int 2) zf x;
    x <- RSBcc x (W32.of_int 2) (! (! zf)) x;
    x <- RSBcc x (arg0 `<<` (W8.of_int 3)) zf x;
    x <- RSBcc x (arg0 `<<` (W8.of_int 3)) (! (! zf)) x;
    x <- RSBcc x (arg0 `>>` (W8.of_int 3)) zf x;
    x <- RSBcc x (arg0 `|>>` (W8.of_int 3)) zf x;
    x <- RSBcc x (arg0 `|>>|` (W8.of_int 3)) zf x;
    res_0 <- x;
    return (res_0);
  }
}.

