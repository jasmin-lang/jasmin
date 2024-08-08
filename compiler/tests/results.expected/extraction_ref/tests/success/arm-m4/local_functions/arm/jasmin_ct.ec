require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc inc (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y + (W32.of_int 1));
    y <- aux;
    return (y);
  }
  
  proc dec (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y - (W32.of_int 1));
    y <- aux;
    return (y);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ inc (a);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ dec (r);
    r <- aux;
    return (r);
  }
}.

