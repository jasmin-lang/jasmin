require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc rol (arg0:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- (arg0 `|<<|` (W8.of_int 0));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `|<<|` (W8.of_int 1));
    x <- (x `|<<|` (W8.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- (zf ? (x `|<<|` (W8.of_int 2)) : x);
    x <- ((! (! zf)) ? (x `|<<|` (W8.of_int 2)) : x);
    res_0 <- x;
    return (res_0);
  }
}.

