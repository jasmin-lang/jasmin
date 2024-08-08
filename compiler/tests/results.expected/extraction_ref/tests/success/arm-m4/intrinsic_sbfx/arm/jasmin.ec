require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc sbfx (arg0:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- SBFX arg0 (W8.of_int 0) (W8.of_int 1);
    x <- SBFX x (W8.of_int 0) (W8.of_int 32);
    x <- SBFX x (W8.of_int 3) (W8.of_int 1);
    x <- SBFX x (W8.of_int 3) (W8.of_int 29);
    x <- SBFX x (W8.of_int 31) (W8.of_int 1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) zf x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (! zf) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) cf x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (! cf) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) nf x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (! nf) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) vf x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (! vf) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (cf /\ (! zf)) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) ((! cf) \/ zf) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (nf = vf) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (! (nf = vf)) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) ((! zf) /\ (nf = vf)) x;
    x <- SBFXcc arg0 (W8.of_int 3) (W8.of_int 5) (zf \/ (! (nf = vf))) x;
    x <- SBFXcc x (W8.of_int 3) (W8.of_int 5) (! (! (! (! zf)))) x;
    res_0 <- x;
    return (res_0);
  }
}.

