require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (in_0:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var x:W128.t;
    var y:W128.t;
    var z:W128.t;
    var xx:W256.t;
    var yy:W256.t;
    var zz:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- PCLMULQDQ x y (W8.of_int 16);
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCLMULQDQ_128 x y (W8.of_int 17);
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    xx <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- xx;
    yy <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPCLMULQDQ_256 xx yy (W8.of_int 1);
    zz <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- xx;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- yy;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- zz;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux_0);
    return ();
  }
}.

