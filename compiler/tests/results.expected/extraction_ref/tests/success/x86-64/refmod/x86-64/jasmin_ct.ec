require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \ule (W64.of_int 0)) ? r : y);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \umod y);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
}.

