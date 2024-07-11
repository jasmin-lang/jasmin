require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.

abbrev glob_0 = Array2.of_list witness [W64.of_int 1; W64.of_int 2].


module M = {
  var leakages : leakages_t
  
  proc load (p:W64.t Array2.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- p.[0];
    r <- aux;
    return (r);
  }
  
  proc test () : W64.t = {
    var aux: W64.t;
    
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ load (glob_0);
    x <- aux;
    return (x);
  }
}.

