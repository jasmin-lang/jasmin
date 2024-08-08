require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc copy (dst:W64.t Array1.t, src:W64.t Array1.t) : W64.t Array1.t = {
    var aux: W64.t;
    
    var tmp:W64.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- src.[0];
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- tmp;
    leakages <- LeakAddr([0]) :: leakages;
    dst.[0] <- aux;
    return (dst);
  }
  
  proc main (x:W64.t) : W64.t = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var result:W64.t;
    var a:W64.t Array1.t;
    var b:W64.t Array1.t;
    a <- witness;
    b <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ copy (b, a);
    b <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    result <- aux;
    return (result);
  }
}.

