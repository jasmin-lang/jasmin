require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test () : int = {
    var aux: int;
    
    var j:int;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- 0;
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (1 `<<` i);
    j <- aux;
    return (j);
  }
  
  proc main () : W32.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var n:W32.t;
    var k:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test ();
    k <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int k);
    n <- aux_0;
    return (n);
  }
}.

