require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc mul (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- MUL arg0 arg1;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, x) <- MULS x arg0;
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- MULcc arg0 arg1 zf x;
    x <- MULcc arg0 arg1 (! zf) x;
    x <- MULcc arg0 arg1 cf x;
    x <- MULcc arg0 arg1 (! cf) x;
    x <- MULcc arg0 arg1 nf x;
    x <- MULcc arg0 arg1 (! nf) x;
    x <- MULcc arg0 arg1 vf x;
    x <- MULcc arg0 arg1 (! vf) x;
    x <- MULcc arg0 arg1 (cf /\ (! zf)) x;
    x <- MULcc arg0 arg1 ((! cf) \/ zf) x;
    x <- MULcc arg0 arg1 (nf = vf) x;
    x <- MULcc arg0 arg1 (! (nf = vf)) x;
    x <- MULcc arg0 arg1 ((! zf) /\ (nf = vf)) x;
    x <- MULcc arg0 arg1 (zf \/ (! (nf = vf))) x;
    res_0 <- x;
    return (res_0);
  }
}.

