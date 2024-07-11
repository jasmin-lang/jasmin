require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W256.t;
    var e:W256.t;
    var f:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSLLDQ_128 a (W8.of_int 1);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSRLDQ_128 b (W8.of_int 2);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 16)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSLLDQ_256 d (W8.of_int 3);
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSRLDQ_256 e (W8.of_int 4);
    f <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- f;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux_0);
    return ();
  }
}.

