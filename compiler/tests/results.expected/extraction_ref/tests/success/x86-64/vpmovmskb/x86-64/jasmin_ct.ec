require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_pmovmskb (tmp:W64.t) : unit = {
    var aux_1: W32.t;
    var aux_2: W64.t;
    var aux: W128.t;
    var aux_0: W256.t;
    
    var x:W128.t;
    var y:W256.t;
    var a:W32.t;
    var b:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_128 ;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_256 ;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- VPMOVMSKB_u128u32 x;
    a <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- a;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- VPMOVMSKB_u128u64 x;
    b <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- b;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux_2);
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- VPMOVMSKB_u256u32 y;
    a <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- a;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- VPMOVMSKB_u256u64 y;
    b <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- b;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux_2);
    return ();
  }
}.

