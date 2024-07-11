require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.

abbrev g = Array2.of_list witness [W64.of_int 1; W64.of_int 2].


module M = {
  var leakages : leakages_t
  
  proc f (a:W64.t Array2.t) : W64.t = {
    var aux: W64.t;
    
    var res_0:W64.t;
    
    leakages <- LeakAddr([1]) :: leakages;
    aux <- a.[1];
    res_0 <- aux;
    return (res_0);
  }
  
  proc main () : W64.t = {
    var aux: W64.t;
    
    var res_0:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f (g);
    res_0 <- aux;
    return (res_0);
  }
}.

