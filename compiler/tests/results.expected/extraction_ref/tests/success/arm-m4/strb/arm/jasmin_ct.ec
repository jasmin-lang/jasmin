require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc strb (arg:W32.t) : unit = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: W8.t;
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
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (arg + (W32.of_int 0))) ((truncateu8 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 3))) ((truncateu8 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 1))))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))) ((truncateu8 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 2))))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))) ((truncateu8 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) ((truncateu8 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 8))))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))) ((truncateu8 aux));
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1) <- CMP x (W32.of_int 0);
    n <- aux_4;
    z <- aux_3;
    c <- aux_2;
    v <- aux_1;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (z ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (c ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! c) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (n ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! n) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (v ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! v) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((c /\ (! z)) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (((! c) \/ z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((n = v) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((! (n = v)) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (((! z) /\ (n = v)) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux_0 <- ((z \/ (! (n = v))) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + arg))));
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + arg)) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 3)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (W32.of_int 3))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 3))))));
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 3)))) (aux_0);
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    aux_0 <- ((! z) ? (truncateu8 x) : (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4))))));
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    Glob.mem <- storeW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))) (aux_0);
    return ();
  }
}.

