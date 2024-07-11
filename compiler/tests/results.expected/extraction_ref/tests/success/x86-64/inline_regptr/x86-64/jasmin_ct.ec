require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc one (a:W64.t Array1.t) : W64.t * W64.t Array1.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    result <- aux;
    return (result, a);
  }
  
  proc main () : W64.t = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var n:W64.t;
    var s:W64.t Array1.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ one (s);
    n <- aux;
    s <- aux_0;
    return (n);
  }
}.

