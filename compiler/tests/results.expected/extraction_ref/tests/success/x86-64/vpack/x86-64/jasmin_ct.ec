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
    aux <- VPACKUS_8u16 x y;
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
    aux <- VPACKUS_4u32 x y;
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
    aux <- VPACKSS_8u16 x y;
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
    aux <- VPACKSS_4u32 x y;
    z <- aux;
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
    aux_0 <- VPACKUS_16u16 xx yy;
    zz <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- zz;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    xx <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- xx;
    yy <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPACKUS_8u32 xx yy;
    zz <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- zz;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    xx <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- xx;
    yy <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPACKSS_16u16 xx yy;
    zz <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- zz;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    xx <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- xx;
    yy <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPACKSS_8u32 xx yy;
    zz <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- zz;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))) (aux_0);
    return ();
  }
}.

