require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc read (ro:W64.t Array1.t) : W64.t = {
    var aux: W64.t;
    
    var v:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- ro.[0];
    v <- aux;
    return (v);
  }
  
  proc write (arg:W64.t Array1.t) : W64.t Array1.t = {
    var aux: W64.t;
    
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    arg.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ read (arg);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    arg.[0] <- aux;
    return (arg);
  }
  
  proc test () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array1.t;
    
    var r:W64.t;
    var s:W64.t Array1.t;
    var rw:W64.t Array1.t;
    rw <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    rw <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ write (rw);
    rw <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rw.[0];
    r <- aux_0;
    return (r);
  }
}.

