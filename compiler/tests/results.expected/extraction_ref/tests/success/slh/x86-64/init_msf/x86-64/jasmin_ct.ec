require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo () : W64.t = {
    var aux: W64.t;
    
    var msf:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    return (msf);
  }
  
  proc foo2 () : unit = {
    var aux: W64.t;
    
    var  _0:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
     _0 <- aux;
    return ();
  }
}.

