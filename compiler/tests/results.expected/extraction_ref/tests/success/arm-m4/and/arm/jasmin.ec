require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc and (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    x <- (arg0 `&` arg1);
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (W32.of_int 1));
    x <- (x `&` (W32.of_int 1));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (W32.of_int (- 1)));
    x <- (x `&` (W32.of_int (- 1)));
    x <- (x `&` (W32.of_int 3402287818));
    x <- (x `&` (W32.of_int 3389049344));
    x <- (x `&` (W32.of_int 13238474));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `<<` (W8.of_int 0)));
    x <- (x `&` (arg0 `<<` (W8.of_int 0)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `<<` (W8.of_int 1)));
    x <- (x `&` (arg0 `<<` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `<<` (W8.of_int 31)));
    x <- (x `&` (arg0 `<<` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `>>` (W8.of_int 1)));
    x <- (x `&` (arg0 `>>` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `>>` (W8.of_int 31)));
    x <- (x `&` (arg0 `>>` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `|>>` (W8.of_int 1)));
    x <- (x `&` (arg0 `|>>` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `|>>` (W8.of_int 31)));
    x <- (x `&` (arg0 `|>>` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `|>>|` (W8.of_int 1)));
    x <- (x `&` (arg0 `|>>|` (W8.of_int 1)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    x <- (arg0 `&` (arg1 `|>>|` (W8.of_int 31)));
    x <- (x `&` (arg0 `|>>|` (W8.of_int 31)));
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (x);
    (nf, zf, cf, vf) <- CMP x (W32.of_int 0);
    x <- (zf ? (arg0 `&` arg1) : x);
    x <- (zf ? (x `&` arg0) : x);
    x <- ((! zf) ? (arg0 `&` arg1) : x);
    x <- ((! zf) ? (x `&` arg0) : x);
    x <- (cf ? (arg0 `&` arg1) : x);
    x <- (cf ? (x `&` arg0) : x);
    x <- ((! cf) ? (arg0 `&` arg1) : x);
    x <- ((! cf) ? (x `&` arg0) : x);
    x <- (nf ? (arg0 `&` arg1) : x);
    x <- (nf ? (x `&` arg0) : x);
    x <- ((! nf) ? (arg0 `&` arg1) : x);
    x <- ((! nf) ? (x `&` arg0) : x);
    x <- (vf ? (arg0 `&` arg1) : x);
    x <- (vf ? (x `&` arg0) : x);
    x <- ((! vf) ? (arg0 `&` arg1) : x);
    x <- ((! vf) ? (x `&` arg0) : x);
    x <- ((cf /\ (! zf)) ? (arg0 `&` arg1) : x);
    x <- ((cf /\ (! zf)) ? (x `&` arg0) : x);
    x <- (((! cf) \/ zf) ? (arg0 `&` arg1) : x);
    x <- (((! cf) \/ zf) ? (x `&` arg0) : x);
    x <- ((nf = vf) ? (arg0 `&` arg1) : x);
    x <- ((nf = vf) ? (x `&` arg0) : x);
    x <- ((! (nf = vf)) ? (arg0 `&` arg1) : x);
    x <- ((! (nf = vf)) ? (x `&` arg0) : x);
    x <- (((! zf) /\ (nf = vf)) ? (arg0 `&` arg1) : x);
    x <- (((! zf) /\ (nf = vf)) ? (x `&` arg0) : x);
    x <- ((zf \/ (! (nf = vf))) ? (arg0 `&` arg1) : x);
    x <- ((zf \/ (! (nf = vf))) ? (x `&` arg0) : x);
    x <- ((! (! (! (! zf)))) ? (x `&` arg0) : x);
    x <- (zf ? (x `&` (W32.of_int 2)) : x);
    x <- ((! (! zf)) ? (x `&` (W32.of_int 2)) : x);
    x <- (zf ? (x `&` (arg0 `<<` (W8.of_int 3))) : x);
    x <- ((! ((! (! zf)) \/ (! (nf = vf)))) ? (x `&` (arg0 `<<` (W8.of_int 3))) : x);
    x <- (zf ? (x `&` (arg0 `>>` (W8.of_int 3))) : x);
    x <- (zf ? (x `&` (arg0 `|>>` (W8.of_int 3))) : x);
    x <- (zf ? (x `&` (arg0 `|>>|` (W8.of_int 3))) : x);
    res_0 <- x;
    return (res_0);
  }
}.

