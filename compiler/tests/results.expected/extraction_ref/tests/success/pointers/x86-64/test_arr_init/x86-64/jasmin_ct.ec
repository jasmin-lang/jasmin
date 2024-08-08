require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc test1 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var a:W64.t Array1.t;
    var b:W64.t Array1.t;
    a <- witness;
    b <- witness;
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
    aux <- (x + b.[0]);
    x <- aux;
    return (x);
  }
  
  proc test2 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var b:W64.t Array1.t;
    var a:W64.t Array1.t;
    a <- witness;
    b <- witness;
    leakages <- LeakCond((x = (W64.of_int 1))) :: LeakAddr([]) :: leakages;
    if ((x = (W64.of_int 1))) {
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
      aux <- (x + b.[0]);
      x <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([0]) :: leakages;
      b.[0] <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- (x + b.[0]);
      x <- aux;
    }
    return (x);
  }
  
  proc test (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test1 (r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test2 (r);
    r <- aux;
    return (r);
  }
}.

