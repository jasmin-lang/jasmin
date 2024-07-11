require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc a__main (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    return (x);
  }
  
  proc b__main (x:W32.t, y:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    x <- aux;
    return (x);
  }
}.

