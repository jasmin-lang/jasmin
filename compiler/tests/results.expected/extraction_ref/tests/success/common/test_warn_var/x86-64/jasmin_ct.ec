require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.

abbrev r = W32.of_int 0.


module M = {
  var leakages : leakages_t
  
  proc fok (r_0:W32.t) : W32.t = {
    var aux: W32.t;
    
    var x:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- r_0;
    x <- aux;
    return (x);
  }
  
  proc f (y:W32.t) : W32.t = {
    var aux: W32.t;
    
    var x:W32.t;
    var y_0:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    x <- aux;
    leakages <- LeakCond((x = (W32.of_int 0))) :: LeakAddr([]) :: leakages;
    if ((x = (W32.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      y_0 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- y_0;
      x <- aux;
    } else {
      
    }
    return (x);
  }
  
  proc g (z:W32.t) : W32.t = {
    var aux: W32.t;
    
    var x:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    x <- aux;
    return (x);
  }
}.

