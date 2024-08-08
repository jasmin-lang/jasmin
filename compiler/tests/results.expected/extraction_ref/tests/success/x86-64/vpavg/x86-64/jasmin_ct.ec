require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_vpavgb (out:W64.t, in_0:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W256.t;
    var e:W256.t;
    var f:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 16)))]) :: leakages;
    aux <- VPAVG_16u8 a (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 16))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPAVG_16u8 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPAVG_16u8 a c;
    d <- zeroextu256(aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (out + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (out + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 32)))]) :: leakages;
    aux_0 <- VPAVG_32u8 d (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 32))));
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPAVG_32u8 d e;
    f <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- f;
    leakages <- LeakAddr([(W64.to_uint (out + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (out + (W64.of_int 32))) (aux_0);
    return ();
  }
  
  proc test_vpavgw (out:W64.t, in_0:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W256.t;
    var e:W256.t;
    var f:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 16)))]) :: leakages;
    aux <- VPAVG_8u16 a (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 16))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPAVG_8u16 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPAVG_8u16 a c;
    d <- zeroextu256(aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (out + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (out + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int 32)))]) :: leakages;
    aux_0 <- VPAVG_16u16 d (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 32))));
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPAVG_16u16 d e;
    f <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- f;
    leakages <- LeakAddr([(W64.to_uint (out + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (out + (W64.of_int 32))) (aux_0);
    return ();
  }
}.

