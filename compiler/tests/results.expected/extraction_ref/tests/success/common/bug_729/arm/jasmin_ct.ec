require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc id (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    return (x);
  }
  
  proc whynot (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ id (a);
    a <- aux;
    return (a);
  }
}.

