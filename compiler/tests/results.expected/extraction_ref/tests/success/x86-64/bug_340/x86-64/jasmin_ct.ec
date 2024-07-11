require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc xor (a:W256.t, b:W256.t) : W256.t = {
    var aux: W256.t;
    
    var c:W256.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a `^` b);
    c <- aux;
    return (c);
  }
  
  proc main (x:W256.t) : W256.t = {
    var aux: W256.t;
    
    var a:W256.t Array1.t;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([0; 0]) :: leakages;
    aux <@ xor (a.[0], a.[0]);
    x <- aux;
    return (x);
  }
}.

