require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo (x:W128.t) : W128.t = {
    var aux: W64.t;
    var aux_0: W128.t;
    
    var y:W128.t;
    var msf:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- protect_128 x msf;
    y <- aux_0;
    return (y);
  }
}.

