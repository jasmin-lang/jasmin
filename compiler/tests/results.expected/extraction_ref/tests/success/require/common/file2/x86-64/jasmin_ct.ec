require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc add (x:W32.t, y:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    r <- aux;
    return (r);
  }
  
  proc main (x:W32.t, y:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r2:W32.t;
    var r1:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ add (x, y);
    r1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r1;
    r2 <- aux;
    return (r2);
  }
}.

