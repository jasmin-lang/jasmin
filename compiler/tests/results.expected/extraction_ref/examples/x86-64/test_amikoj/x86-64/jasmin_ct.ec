require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var c:W64.t;
    var a:W64.t;
    var b:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (b + a);
    c <- aux;
    return (c);
  }
}.

