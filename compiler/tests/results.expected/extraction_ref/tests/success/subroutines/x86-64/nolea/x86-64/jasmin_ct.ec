require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc id (x:W32.t) : W32.t = {
    
    
    
    
    return (x);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ id (r);
    r <- aux;
    return (r);
  }
}.

