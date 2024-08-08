require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array5.
require import WArray20.



module M = {
  var leakages : leakages_t
  
  proc array_init () : W32.t Array5.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var a:W32.t Array5.t;
    var i:int;
    a <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W32.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc test_u16 () : W16.t = {
    var aux_2: W16.t;
    var aux_1: W32.t;
    var aux_0: W64.t;
    var aux: W32.t Array5.t;
    
    var r:W16.t;
    var a:W32.t Array5.t;
    var i:W64.t;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ array_init ();
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W32.of_int 3);
    leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
    a.[(W64.to_uint i)] <- aux_1;
    leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
    aux_2 <- (get16 (WArray20.init32 (fun i_0 => (a).[i_0])) (W64.to_uint i));
    r <- aux_2;
    return (r);
  }
  
  proc test_u32 () : W32.t = {
    var aux_0: W32.t;
    var aux_1: W64.t;
    var aux: W32.t Array5.t;
    
    var r:W32.t;
    var a:W32.t Array5.t;
    var i:W64.t;
    var t:W32.t;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ array_init ();
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W64.of_int 0);
    i <- aux_1;
    
    leakages <- LeakCond((i \ult (W64.of_int 5))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 5))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_0 <- a.[(W64.to_uint i)];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (r + t);
      r <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (i + (W64.of_int 1));
      i <- aux_1;
    leakages <- LeakCond((i \ult (W64.of_int 5))) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
}.

