require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc inc (x:int) : int = {
    var aux: int;
    
    var y:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + 1);
    y <- aux;
    return (y);
  }
  
  proc snd (a:W64.t, b:W64.t) : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var r:W64.t;
    var t:W64.t Array2.t;
    var k:int;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ inc (0);
    k <- aux_0;
    leakages <- LeakAddr([k]) :: leakages;
    aux <- t.[k];
    r <- aux;
    return (r);
  }
}.

