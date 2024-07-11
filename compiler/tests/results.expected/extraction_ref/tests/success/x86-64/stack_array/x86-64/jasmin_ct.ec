require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array10.
require import WArray80.



module M = {
  var leakages : leakages_t
  
  proc fill (in_0:W64.t, out:W64.t, len:W64.t) : W64.t = {
    var aux_0: W64.t;
    
    var i:W64.t;
    var max:W64.t;
    var aux:W64.t;
    var t:W64.t Array10.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 10);
    max <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((len \ult max) ? len : max);
    max <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    i <- aux_0;
    
    leakages <- LeakCond((i \ult max)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult max)) {
      leakages <- LeakAddr([(W64.to_uint (in_0 + ((W64.of_int 8) * i)))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))));
      aux <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- aux;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      t.[(W64.to_uint i)] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W64.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult max)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    i <- aux_0;
    
    leakages <- LeakCond((i \ult max)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult max)) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_0 <- t.[(W64.to_uint i)];
      aux <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- aux;
      leakages <- LeakAddr([(W64.to_uint (in_0 + ((W64.of_int 8) * i)))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))) (aux_0);
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W64.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult max)) :: LeakAddr([]) :: leakages;
    
    }
    return (i);
  }
}.

