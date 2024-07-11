require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc ldrsb (arg:W32.t) : W32.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W32.t;
    
    var res_0:W32.t;
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    leakages <- LeakAddr([(W32.to_uint (arg + (W32.of_int 0)))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (arg + (W32.of_int 0)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 3)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 3))))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 1))))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1))))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 2))))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2))))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4))))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 8))))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8))))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP x (W32.of_int 0);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    v <- aux_0;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (z ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! z) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (c ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! c) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (n ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! n) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (v ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! v) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((c /\ (! z)) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (((! c) \/ z) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((n = v) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! (n = v)) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (((! z) /\ (n = v)) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((z \/ (! (n = v))) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    aux <- ((! z) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + arg)))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    aux <- ((! z) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 3))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    aux <- ((! z) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))))) : x);
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    aux <- ((! z) ? (sigextu32 (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))))) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    res_0 <- aux;
    return (res_0);
  }
}.

