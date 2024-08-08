require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_imm (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var y:W64.t;
    var g:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 42);
    g <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y + g);
    y <- aux;
    return (y);
  }
}.

