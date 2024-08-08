require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc inc (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- LEA_64 (x + (W64.of_int 1));
    x <- aux;
    return (x);
  }
  
  proc one () : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ inc ((W64.of_int 0));
    r <- aux;
    return (r);
  }
}.

