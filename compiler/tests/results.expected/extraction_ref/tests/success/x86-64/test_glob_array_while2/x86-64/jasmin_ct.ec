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
    var aux: W64.t;
    var aux_0: W64.t Array4.t;
    
    var r:W64.t;
    var i:W64.t;
    var gt1:W64.t Array4.t;
    gt1 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_t;
    gt1 <- aux_0;
    
    leakages <- LeakCond((i \ult (W64.of_int 4))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 4))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- (r + gt1.[(W64.to_uint i)]);
      r <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult (W64.of_int 4))) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
}.

