require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc smlal (arg0:W32.t, arg1:W32.t) : W32.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: W32.t;
    var aux: W32.t;
    
    var res_0:W32.t;
    var x:W32.t;
    var y:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLAL x y arg0 arg1;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1) <- CMP x (W32.of_int 0);
    n <- aux_4;
    z <- aux_3;
    c <- aux_2;
    v <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 z x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (! z) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 c x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (! c) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 n x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (! n) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 v x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (! v) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (c /\ (! z)) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 ((! c) \/ z) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (n = v) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (! (n = v)) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 ((! z) /\ (n = v)) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- SMLALcc x y x arg0 (z \/ (! (n = v))) x y;
    x <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    res_0 <- aux_0;
    return (res_0);
  }
}.

