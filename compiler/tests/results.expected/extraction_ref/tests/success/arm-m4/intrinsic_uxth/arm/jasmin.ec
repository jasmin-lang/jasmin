require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc uxth (arg0:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- UXTH arg0 (W8.of_int 0);
    x <- UXTH x (W8.of_int 8);
    x <- UXTH x (W8.of_int 16);
    x <- UXTH x (W8.of_int 24);
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- UXTHcc arg0 (W8.of_int 8) zf x;
    x <- UXTHcc arg0 (W8.of_int 8) (! zf) x;
    x <- UXTHcc arg0 (W8.of_int 8) cf x;
    x <- UXTHcc arg0 (W8.of_int 8) (! cf) x;
    x <- UXTHcc arg0 (W8.of_int 8) nf x;
    x <- UXTHcc arg0 (W8.of_int 8) (! nf) x;
    x <- UXTHcc arg0 (W8.of_int 8) vf x;
    x <- UXTHcc arg0 (W8.of_int 8) (! vf) x;
    x <- UXTHcc arg0 (W8.of_int 8) (cf /\ (! zf)) x;
    x <- UXTHcc arg0 (W8.of_int 8) ((! cf) \/ zf) x;
    x <- UXTHcc arg0 (W8.of_int 8) (nf = vf) x;
    x <- UXTHcc arg0 (W8.of_int 8) (! (nf = vf)) x;
    x <- UXTHcc arg0 (W8.of_int 8) ((! zf) /\ (nf = vf)) x;
    x <- UXTHcc arg0 (W8.of_int 8) (zf \/ (! (nf = vf))) x;
    x <- UXTHcc arg0 (W8.of_int 8) (! (! (! (! zf)))) x;
    res_0 <- x;
    return (res_0);
  }
}.

