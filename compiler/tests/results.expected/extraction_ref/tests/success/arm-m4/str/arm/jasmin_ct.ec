require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc str (arg:W32.t) : unit = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W32.t;
    
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- arg;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (arg + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (arg + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 1))))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 2))))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 8))))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP x (W32.of_int 0);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    v <- aux_0;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (c ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! c) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (n ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! n) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (v ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! v) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((c /\ (! z)) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (((! c) \/ z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((n = v) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((! (n = v)) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (((! z) /\ (n = v)) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- ((z \/ (! (n = v))) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    aux <- ((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + arg))));
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + arg)) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    aux <- ((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 3)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    aux <- ((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (- (W32.of_int 3))))));
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (aux);
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    aux <- ((! z) ? x : (loadW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4))))));
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (aux);
    return ();
  }
}.

