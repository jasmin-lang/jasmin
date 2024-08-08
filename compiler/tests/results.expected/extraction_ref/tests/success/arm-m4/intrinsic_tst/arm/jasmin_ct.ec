require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc tst (arg0:W32.t, arg1:W32.t, p:W32.t) : unit = {
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
    aux <- (W32.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TST arg0 arg1;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (n ? (W32.of_int 1) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (p + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TST arg0 (W32.of_int 3);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TST x (W32.of_int 3402287818);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TST x (W32.of_int 3389049344);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TST x (W32.of_int 13238474);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    aux <- (z ? x : (loadW32 Glob.mem (W32.to_uint (x + (W32.of_int 0)))));
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP arg0 (W32.of_int 0);
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 z n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (! z) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 c n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (! c) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 n n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (! n) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 v n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (! v) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (c /\ (! z)) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 ((! c) \/ z) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (n = v) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (! (n = v)) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 ((! z) /\ (n = v)) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 arg1 (z \/ (! (n = v))) n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1) <- TSTcc arg0 (W32.of_int 3) z n z c;
    n <- aux_3;
    z <- aux_2;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (n ? (W32.of_int 1) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (p + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))) (aux);
    return ();
  }
}.

