require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

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
    var t:W32.t;
    a <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W32.of_int i);
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc test_u16 () : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t Array5.t;
    
    var r:W32.t;
    var a:W32.t Array5.t;
    var pa:W32.t Array5.t;
    var i:W32.t;
    var t:W32.t;
    a <- witness;
    pa <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ array_init ();
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    pa <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 3);
    t <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- t;
    leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
    pa.[(W32.to_uint i)] <- aux_0;
    leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
    aux_0 <- (zeroextu32 (get16 (WArray20.init32 (fun i_0 => (pa).[i_0])) (W32.to_uint i)));
    r <- aux_0;
    return (r);
  }
  
  proc test_u32 () : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t Array5.t;
    
    var r:W32.t;
    var a:W32.t Array5.t;
    var pa:W32.t Array5.t;
    var i:W32.t;
    var t:W32.t;
    a <- witness;
    pa <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ array_init ();
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    pa <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    i <- aux_0;
    
    leakages <- LeakCond((i \ult (W32.of_int 5))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W32.of_int 5))) {
      leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
      aux_0 <- pa.[(W32.to_uint i)];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (r + t);
      r <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W32.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult (W32.of_int 5))) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
}.

