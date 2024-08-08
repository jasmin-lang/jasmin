require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.

abbrev g = Array2.of_list witness [W64.of_int 1; W64.of_int 0].


module M = {
  var leakages : leakages_t
  
  proc load (p:W64.t Array2.t, i:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
    aux <- p.[(W64.to_uint i)];
    r <- aux;
    return (r);
  }
  
  proc main (z:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var result:W64.t;
    var i:int;
    var stk:W64.t Array2.t;
    var n:W64.t;
    stk <- witness;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- z;
      leakages <- LeakAddr([i]) :: leakages;
      stk.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    n <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ load (g, n);
    n <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ load (stk, n);
    result <- aux_0;
    return (result);
  }
}.

