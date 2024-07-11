require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc aes_test (p:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W128.t;
    
    var r:W64.t;
    var x1:W128.t;
    var x2:W128.t;
    var x3:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_128 ;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_128 ;
    x2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- AESENC x1 x2;
    x1 <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- AESENC x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESENC_128 x1 x2;
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x3;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VAESENC_128 x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x3;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- AESDEC x1 x2;
    x1 <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- AESDEC x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESDEC_128 x1 x2;
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x3;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VAESDEC_128 x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x3;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- AESIMC x1;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESIMC x1;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- AESIMC (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x1 <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VAESIMC (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- AESKEYGENASSIST x1 (W8.of_int 5);
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- AESKEYGENASSIST x3 (W8.of_int 4);
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x3;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- AESKEYGENASSIST (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0)))) (W8.of_int 3);
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESKEYGENASSIST x1 (W8.of_int 1);
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESKEYGENASSIST x3 (W8.of_int 2);
    x3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x3;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VAESKEYGENASSIST (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0)))) (W8.of_int 0);
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    return (r);
  }
  
  proc test_vaes (p:W64.t) : unit = {
    var aux: W256.t;
    
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux <- VAESENC_256 x (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESENC_256 y x;
    z <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 64)))]) :: leakages;
    aux <- VAESENCLAST_256 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESENCLAST_256 x y;
    y <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux <- VAESDEC_256 y (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESDEC_256 z y;
    x <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VAESDECLAST_256 x (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VAESDECLAST_256 y x;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
}.

