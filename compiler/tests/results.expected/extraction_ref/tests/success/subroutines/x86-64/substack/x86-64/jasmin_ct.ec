require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc double (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var y:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    x <- aux;
    return (x);
  }
  
  proc main (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ double (r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ double (r);
    r <- aux;
    return (r);
  }
}.

