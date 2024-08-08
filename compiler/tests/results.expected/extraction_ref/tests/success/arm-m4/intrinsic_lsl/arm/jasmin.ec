require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc lsl (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- LSL arg0 (truncateu8 arg1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- LSL arg0 (W8.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, x) <- LSLS x (truncateu8 arg0);
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- LSLcc arg0 (truncateu8 arg1) zf x;
    x <- LSLcc arg0 (truncateu8 arg1) (! zf) x;
    x <- LSLcc arg0 (truncateu8 arg1) cf x;
    x <- LSLcc arg0 (truncateu8 arg1) (! cf) x;
    x <- LSLcc arg0 (truncateu8 arg1) nf x;
    x <- LSLcc arg0 (truncateu8 arg1) (! nf) x;
    x <- LSLcc arg0 (truncateu8 arg1) vf x;
    x <- LSLcc arg0 (truncateu8 arg1) (! vf) x;
    x <- LSLcc arg0 (truncateu8 arg1) (cf /\ (! zf)) x;
    x <- LSLcc arg0 (truncateu8 arg1) ((! cf) \/ zf) x;
    x <- LSLcc arg0 (truncateu8 arg1) (nf = vf) x;
    x <- LSLcc arg0 (truncateu8 arg1) (! (nf = vf)) x;
    x <- LSLcc arg0 (truncateu8 arg1) ((! zf) /\ (nf = vf)) x;
    x <- LSLcc arg0 (truncateu8 arg1) (zf \/ (! (nf = vf))) x;
    (nf, zf, cf, x) <- LSLScc x (truncateu8 arg0) (nf = vf) nf zf cf x;
    (nf, zf, cf, x) <- LSLS x (W8.of_int 2);
    (nf, zf, cf, x) <- LSLScc x (W8.of_int 2) (nf = vf) nf zf cf x;
    x <- LSLcc x (truncateu8 arg0) (! (! (! (! zf)))) x;
    x <- LSLcc x (W8.of_int 2) zf x;
    x <- LSLcc x (W8.of_int 2) (! (! zf)) x;
    res_0 <- x;
    return (res_0);
  }
}.

