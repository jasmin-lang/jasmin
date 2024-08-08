require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.

abbrev g = Array2.of_list witness [W64.of_int 1; W64.of_int 2].


module M = {
  var leakages : leakages_t
  
  proc main () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array2.t;
    
    var res_0:W64.t;
    var s:W64.t Array2.t;
    var r:W64.t Array2.t;
    r <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- g;
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r.[0];
    res_0 <- aux_0;
    return (res_0);
  }
}.

