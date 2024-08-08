require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc cond_swap (p:W32.t, q:W32.t, cond:W32.t) : unit = {
    var aux: bool;
    var aux_0: W32.t;
    
    var f:bool;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var d:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (cond <> (W32.of_int 0));
    f <- aux;
    leakages <- LeakAddr([(W32.to_uint (p + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (loadW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))));
    a <- aux_0;
    leakages <- LeakAddr([(W32.to_uint (q + (W32.of_int 0)))]) :: leakages;
    aux_0 <- (loadW32 Glob.mem (W32.to_uint (q + (W32.of_int 0))));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (f ? b : c);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (f ? a : d);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((! f) ? a : c);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((! f) ? b : d);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- c;
    leakages <- LeakAddr([(W32.to_uint (p + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))) (aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- d;
    leakages <- LeakAddr([(W32.to_uint (q + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (q + (W32.of_int 0))) (aux_0);
    return ();
  }
}.

