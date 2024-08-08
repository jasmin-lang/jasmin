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
    
    x <- (invw arg0);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (W32.of_int 4294967294);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (W32.of_int 4294967040);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `<<` (W8.of_int 0)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `<<` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `<<` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `>>` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `>>` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `|>>` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `|>>` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `|>>|` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (invw (arg0 `|>>|` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- (zf ? (invw arg0) : x);
    x <- ((! zf) ? (invw arg0) : x);
    x <- (cf ? (invw arg0) : x);
    x <- ((! cf) ? (invw arg0) : x);
    x <- (nf ? (invw arg0) : x);
    x <- ((! nf) ? (invw arg0) : x);
    x <- (vf ? (invw arg0) : x);
    x <- ((! vf) ? (invw arg0) : x);
    x <- ((cf /\ (! zf)) ? (invw arg0) : x);
    x <- (((! cf) \/ zf) ? (invw arg0) : x);
    x <- ((nf = vf) ? (invw arg0) : x);
    x <- ((! (nf = vf)) ? (invw arg0) : x);
    x <- (((! zf) /\ (nf = vf)) ? (invw arg0) : x);
    x <- ((zf \/ (! (nf = vf))) ? (invw arg0) : x);
    x <- ((! (! (! (! zf)))) ? (invw arg0) : x);
    x <- (zf ? (invw (W32.of_int 2)) : x);
    x <- ((! (! zf)) ? (invw (W32.of_int 2)) : x);
    x <- (zf ? (invw (arg0 `<<` (W8.of_int 3))) : x);
    x <- ((! ((! (! zf)) \/ (! (nf = vf)))) ? (invw (arg0 `<<` (W8.of_int 3))) : x);
    x <- (zf ? (invw (arg0 `>>` (W8.of_int 3))) : x);
    x <- (zf ? (invw (arg0 `|>>` (W8.of_int 3))) : x);
    x <- (zf ? (invw (arg0 `|>>|` (W8.of_int 3))) : x);
    res_0 <- x;
    return (res_0);
  }
}.

