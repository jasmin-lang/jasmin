require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc aux (x:W32.t) : W32.t = {
    var aux_0: W32.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    y <- aux_0;
    return (y);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux_0: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ aux (a);
    a <- aux_0;
    return (a);
  }
}.

