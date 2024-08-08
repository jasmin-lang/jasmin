require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc uxtb (arg0:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- UXTB arg0 (W8.of_int 0);
    x <- UXTB x (W8.of_int 8);
    x <- UXTB x (W8.of_int 16);
    x <- UXTB x (W8.of_int 24);
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- UXTBcc arg0 (W8.of_int 8) zf x;
    x <- UXTBcc arg0 (W8.of_int 8) (! zf) x;
    x <- UXTBcc arg0 (W8.of_int 8) cf x;
    x <- UXTBcc arg0 (W8.of_int 8) (! cf) x;
    x <- UXTBcc arg0 (W8.of_int 8) nf x;
    x <- UXTBcc arg0 (W8.of_int 8) (! nf) x;
    x <- UXTBcc arg0 (W8.of_int 8) vf x;
    x <- UXTBcc arg0 (W8.of_int 8) (! vf) x;
    x <- UXTBcc arg0 (W8.of_int 8) (cf /\ (! zf)) x;
    x <- UXTBcc arg0 (W8.of_int 8) ((! cf) \/ zf) x;
    x <- UXTBcc arg0 (W8.of_int 8) (nf = vf) x;
    x <- UXTBcc arg0 (W8.of_int 8) (! (nf = vf)) x;
    x <- UXTBcc arg0 (W8.of_int 8) ((! zf) /\ (nf = vf)) x;
    x <- UXTBcc arg0 (W8.of_int 8) (zf \/ (! (nf = vf))) x;
    x <- UXTBcc arg0 (W8.of_int 8) (! (! (! (! zf)))) x;
    res_0 <- x;
    return (res_0);
  }
}.

