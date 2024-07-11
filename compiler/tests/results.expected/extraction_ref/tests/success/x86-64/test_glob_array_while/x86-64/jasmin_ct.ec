require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray32.

abbrev glob_t = Array4.of_list witness [W64.of_int 0; W64.of_int 1; W64.of_int 2; W64.of_int 3].


module M = {
  var leakages : leakages_t
  
  proc sum (x:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array4.t;
    
    var r:W64.t;
    var gt1:W64.t Array4.t;
    var gt2:W64.t Array4.t;
    var i:W64.t;
    gt1 <- witness;
    gt2 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- glob_t;
    gt1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- gt1;
    gt2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    i <- aux_0;
    
    leakages <- LeakCond((i \ult (W64.of_int 4))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 4))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_0 <- (r + gt1.[(W64.to_uint i)]);
      r <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W64.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult (W64.of_int 4))) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    i <- aux_0;
    
    leakages <- LeakCond((i \ult (W64.of_int 4))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 4))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_0 <- (r + gt2.[(W64.to_uint i)]);
      r <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W64.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult (W64.of_int 4))) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
}.

