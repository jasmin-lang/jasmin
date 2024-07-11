require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc mov (arg0:W32.t) : W32.t = {
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
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- arg0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 3402287818);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 3389049344);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 13238474);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 51968);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 51914);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP x (W32.of_int 0);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (z ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! z) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! c) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (n ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! n) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (v ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! v) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((c /\ (! z)) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((! c) \/ z) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((n = v) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! (n = v)) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((! z) /\ (n = v)) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((z \/ (! (n = v))) ? arg0 : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? (W32.of_int 1) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? (W32.of_int 3402287818) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? (W32.of_int 3389049344) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? (W32.of_int 13238474) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? (W32.of_int 51968) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? (W32.of_int 51914) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    res_0 <- aux;
    return (res_0);
  }
}.

