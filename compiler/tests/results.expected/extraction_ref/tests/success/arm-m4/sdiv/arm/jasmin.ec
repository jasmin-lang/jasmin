require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc sdiv (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- (arg0 \sdiv arg1);
    (n, z, c, v) <- CMP x (W32.of_int 0);
    x <- (z ? (x \sdiv arg0) : x);
    x <- ((! z) ? (x \sdiv arg0) : x);
    x <- (c ? (x \sdiv arg0) : x);
    x <- ((! c) ? (x \sdiv arg0) : x);
    x <- (n ? (x \sdiv arg0) : x);
    x <- ((! n) ? (x \sdiv arg0) : x);
    x <- (v ? (x \sdiv arg0) : x);
    x <- ((! v) ? (x \sdiv arg0) : x);
    x <- ((c /\ (! z)) ? (x \sdiv arg0) : x);
    x <- (((! c) \/ z) ? (x \sdiv arg0) : x);
    x <- ((n = v) ? (x \sdiv arg0) : x);
    x <- ((! (n = v)) ? (x \sdiv arg0) : x);
    x <- (((! z) /\ (n = v)) ? (x \sdiv arg0) : x);
    x <- ((z \/ (! (n = v))) ? (x \sdiv arg0) : x);
    res_0 <- x;
    return (res_0);
  }
}.

