require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var a:W64.t Array1.t;
    var b:W64.t Array1.t;
    a <- witness;
    b <- witness;
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    if (((W64.of_int 0) \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([0]) :: leakages;
      a.[0] <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- (x + a.[0]);
      x <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([0]) :: leakages;
      b.[0] <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- b.[0];
      r <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([0]) :: leakages;
      a.[0] <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- (x + a.[0]);
      x <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([0]) :: leakages;
      b.[0] <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- b.[0];
      r <- aux;
    }
    return (r);
  }
  
  proc main (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f (x);
    result <- aux;
    return (result);
  }
}.

