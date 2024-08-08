require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc addn (r:W64.t, n:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + n);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (n + n));
    r <- aux;
    return (r);
  }
  
  proc f (r1:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ addn (r, (W64.of_int 6));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ addn (r, (W64.of_int 3));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ addn (r, (W64.of_int 5));
    r <- aux;
    return (r);
  }
}.

