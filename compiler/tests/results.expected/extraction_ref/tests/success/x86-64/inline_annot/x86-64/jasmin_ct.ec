require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f1 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + (W64.of_int 1));
    x <- aux;
    return (x);
  }
  
  proc f2 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + (W64.of_int 2));
    x <- aux;
    return (x);
  }
  
  proc foo (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f1 (x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f2 (x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f1 (x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    return (r);
  }
}.

