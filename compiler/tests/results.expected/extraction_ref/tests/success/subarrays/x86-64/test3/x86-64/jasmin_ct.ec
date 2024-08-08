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
    
    
    
    
    return (x);
  }
  
  proc good () : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var t:W64.t;
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f2 (t);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    return (r);
  }
}.

