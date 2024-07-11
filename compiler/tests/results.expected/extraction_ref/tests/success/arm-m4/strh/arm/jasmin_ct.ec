require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc strh (arg:W32.t) : unit = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: W16.t;
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
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg + (W32.of_int 0))) ((truncateu16 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 3))) ((truncateu16 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 1))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))) ((truncateu16 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 2))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))) ((truncateu16 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) ((truncateu16 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 8))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))) ((truncateu16 aux));
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1) <- CMP x (W32.of_int 0);
    n <- aux_4;
    z <- aux_3;
    c <- aux_2;
    v <- aux_1;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (z ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (c ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! c) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (n ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! n) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (v ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! v) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((c /\ (! z)) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (((! c) \/ z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((n = v) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! (n = v)) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (((! z) /\ (n = v)) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((z \/ (! (n = v))) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + arg))));
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + arg)) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 3)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 3))))));
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu16 x) : (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4))))));
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (aux_0);
    return ();
  }
}.

