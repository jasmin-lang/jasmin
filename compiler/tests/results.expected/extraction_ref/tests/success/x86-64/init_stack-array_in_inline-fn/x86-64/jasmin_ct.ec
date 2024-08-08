require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t Array1.t, n:W64.t) : W64.t Array1.t = {
    var aux: W64.t;
    
    var y:W64.t Array1.t;
    y <- witness;
    
    leakages <- LeakCond(((W64.of_int 0) \ult n)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult n)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 0);
      leakages <- LeakAddr([0]) :: leakages;
      y.[0] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (n - (W64.of_int 1));
      n <- aux;
    leakages <- LeakCond(((W64.of_int 0) \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    return (y);
  }
  
  proc main (p:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array1.t;
    
    var r:W64.t;
    var x:W64.t Array1.t;
    x <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f (x, p);
    x <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- x.[0];
    r <- aux_0;
    return (r);
  }
}.

