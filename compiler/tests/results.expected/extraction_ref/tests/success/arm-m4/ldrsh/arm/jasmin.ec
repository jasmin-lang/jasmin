require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc ldrsh (arg:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (arg + (W32.of_int 0)))));
    x <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 3)))));
    x <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 3))))));
    x <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1))))));
    x <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2))))));
    x <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4))))));
    x <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8))))));
    (n, z, c, v) <- CMP x (W32.of_int 0);
    x <- (z ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((! z) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- (c ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((! c) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- (n ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((! n) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- (v ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((! v) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((c /\ (! z)) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- (((! c) \/ z) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((n = v) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((! (n = v)) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- (((! z) /\ (n = v)) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((z \/ (! (n = v))) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- ((! z) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + arg)))) : x);
    x <- ((! z) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 3))))) : x);
    x <- ((! z) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))))) : x);
    x <- ((! z) ? (sigextu32 (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))))) : x);
    res_0 <- x;
    return (res_0);
  }
}.

