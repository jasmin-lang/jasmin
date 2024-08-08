require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo (x:W64.t, y:W64.t) : W64.t * W64.t = {
    var aux: W64.t;
    
    var r1:W64.t;
    var r2:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    r2 <- aux;
    return (r1, r2);
  }
  
  proc foo2 (x:W64.t, y:W64.t) : W64.t * W64.t = {
    var aux: W64.t;
    
    var r1:W64.t;
    var r2:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    r2 <- aux;
    return (r1, r2);
  }
  
  proc foo1 (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r1:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r1 <- aux;
    return (r1);
  }
}.

