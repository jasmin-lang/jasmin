require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc test_sum_u8 (ptr_:W64.t, len:W64.t) : W8.t = {
    var aux: W8.t;
    var aux_0: W64.t;
    
    var r:W8.t;
    var off:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    off <- aux_0;
    
    leakages <- LeakCond((off \ult len)) :: LeakAddr([]) :: leakages;
    
    while ((off \ult len)) {
      leakages <- LeakAddr([(W64.to_uint (ptr_ + off))]) :: leakages;
      aux <- (r + (loadW8 Glob.mem (W64.to_uint (ptr_ + off))));
      r <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (off + (W64.of_int 1));
      off <- aux_0;
    leakages <- LeakCond((off \ult len)) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
  
  proc test_xor_u16 (ptr_:W64.t, len:W64.t) : W16.t = {
    var aux: W16.t;
    var aux_0: W64.t;
    
    var r:W16.t;
    var off:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W16.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    off <- aux_0;
    
    leakages <- LeakCond((off \ult len)) :: LeakAddr([]) :: leakages;
    
    while ((off \ult len)) {
      leakages <- LeakAddr([(W64.to_uint (ptr_ + (off * (W64.of_int 2))))]) :: leakages;
      aux <- (r `^` (loadW16 Glob.mem (W64.to_uint (ptr_ + (off * (W64.of_int 2))))));
      r <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (off + (W64.of_int 1));
      off <- aux_0;
    leakages <- LeakCond((off \ult len)) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
  
  proc test_swap_u32 (ptr_:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W32.t;
    var aux_1: W64.t;
    
    var z:W64.t;
    var i:int;
    var w:W32.t Array2.t;
    w <- witness;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([(W64.to_uint (ptr_ + (W64.of_int (i * 4))))]) :: leakages;
      aux_0 <- (loadW32 Glob.mem (W64.to_uint (ptr_ + (W64.of_int (i * 4)))));
      leakages <- LeakAddr([i]) :: leakages;
      w.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- w.[i];
      leakages <- LeakAddr([(W64.to_uint (ptr_ + (W64.of_int ((1 - i) * 4))))]) :: leakages;
      Glob.mem <- storeW32 Glob.mem (W64.to_uint (ptr_ + (W64.of_int ((1 - i) * 4)))) (aux_0);
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W64.of_int 0);
    z <- aux_1;
    return (z);
  }
  
  proc test_u128 (ptr_:W64.t) : W64.t = {
    var aux: W64.t;
    var aux_0: W128.t;
    
    var r:W64.t;
    var t:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakAddr([(W64.to_uint (ptr_ + (W64.of_int (16 * 0))))]) :: leakages;
    aux_0 <- (loadW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int (16 * 0)))));
    t <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- t;
    leakages <- LeakAddr([(W64.to_uint (ptr_ + (W64.of_int (16 * 1))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int (16 * 1)))) (aux_0);
    return (r);
  }
}.

