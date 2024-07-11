require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var ms:W64.t;
    var _ms:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    ms <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- mov_msf ms;
    _ms <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- mov_msf _ms;
    ms <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x ms;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    return (x);
  }
}.

