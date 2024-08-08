require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc strh (arg0:W32.t, arg1:W32.t) : unit = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W16.t;
    
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- STRH (truncateu16 arg0);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- STRH (truncateu16 arg0);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 2)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 2))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- STRH (truncateu16 arg0);
    leakages <- LeakAddr([(W32.to_uint (arg0 + arg1))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + arg1)) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- STRH (truncateu16 arg0);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (arg1 * (W32.of_int 1))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 1)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- STRH (truncateu16 arg0);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (arg1 * (W32.of_int 2))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- STRH (truncateu16 arg0);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (arg1 * (W32.of_int 4))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 4)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- STRH (truncateu16 arg0);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (arg1 * (W32.of_int 8))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 8)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP arg0 (W32.of_int 0);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    v <- aux_0;
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (! z) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) c (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (! c) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) n (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (! n) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) v (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (! v) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (c /\ (! z)) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) ((! c) \/ z) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (n = v) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (! (n = v)) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) ((! z) /\ (n = v)) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) (z \/ (! (n = v))) (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + arg1))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + arg1)));
    leakages <- LeakAddr([(W32.to_uint (arg0 + arg1))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + arg1)) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 3)))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (W32.of_int 3)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (W32.of_int 3))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (- (W32.of_int 3))))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3)))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (- (W32.of_int 3))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (- (W32.of_int 3)))) (aux);
    leakages <- LeakAddr([(W32.to_uint (arg0 + (arg1 * (W32.of_int 2))))]) :: leakages;
    aux <- STRHcc (truncateu16 arg0) z (loadW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))));
    leakages <- LeakAddr([(W32.to_uint (arg0 + (arg1 * (W32.of_int 2))))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W32.to_uint (arg0 + (arg1 * (W32.of_int 2)))) (aux);
    return ();
  }
}.

