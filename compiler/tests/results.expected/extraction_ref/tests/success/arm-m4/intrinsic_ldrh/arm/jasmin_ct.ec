require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc ldrh (arg:W32.t) : W32.t = {
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
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (arg + (W32.of_int 0))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 2)))]) :: leakages;
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 2))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 2))))]) :: leakages;
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 2)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (x + arg)));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 1))))]) :: leakages;
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 2))))]) :: leakages;
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 4))))]) :: leakages;
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 8))))]) :: leakages;
    aux <- LDRH (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP x (W32.of_int 0);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    v <- aux_0;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) z x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! z) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) c x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! c) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) n x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! n) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) v x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! v) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (c /\ (! z)) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) ((! c) \/ z) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (n = v) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! (n = v)) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) ((! z) /\ (n = v)) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (z \/ (! (n = v))) x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + arg))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + arg))) z x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 3)))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (W32.of_int 3)))) z x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (- (W32.of_int 3))))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (- (W32.of_int 3))))) z x;
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (x + (arg * (W32.of_int 2))))]) :: leakages;
    aux <- LDRHcc (loadW16 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2))))) z x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    res_0 <- aux;
    return (res_0);
  }
}.

