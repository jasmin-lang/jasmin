require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_vpcmpgt (tmp:W64.t) : unit = {
    var aux_0: W128.t;
    var aux: W256.t;
    
    var y:W256.t;
    var x:W256.t;
    var z:W256.t;
    var i:W128.t;
    var j:W128.t;
    var k:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCMPGT_32u8 x y;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_128 ;
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_128 ;
    j <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPCMPGT_8u16 i j;
    k <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- k;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (tmp + (W64.of_int 32))) (aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCMPGT_8u32 x y;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 64)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 64))) (aux);
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPCMPGT_2u64 i (loadW128 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))));
    j <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPCMPGT_2u64 i j;
    k <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- k;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    aux <- VPCMPGT_4u64 x (loadW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCMPGT_4u64 x y;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_vpcmpeq (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var i:W128.t;
    var j:W128.t;
    var k:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    i <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPCMPEQ_16u8 i (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    j <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCMPEQ_16u8 i j;
    k <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPCMPEQ_8u16 k (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCMPEQ_8u16 i j;
    k <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPCMPEQ_4u32 k (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    j <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCMPEQ_4u32 i j;
    k <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPCMPEQ_2u64 k (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    j <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPCMPEQ_2u64 i j;
    k <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- k;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPCMPEQ_32u8 x (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPCMPEQ_32u8 x y;
    z <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPCMPEQ_16u16 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPCMPEQ_16u16 x y;
    z <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPCMPEQ_8u32 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPCMPEQ_8u32 x y;
    z <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPCMPEQ_4u64 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPCMPEQ_4u64 x y;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_0);
    return ();
  }
}.

