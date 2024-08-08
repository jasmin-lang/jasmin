require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc load (p:W64.t) : W64.t = {
    var aux: W64.t;
    
    var x:W64.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux;
    return (x);
  }
  
  proc main (cptr:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    var tmp:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- cptr;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ load (tmp);
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (result + tmp);
    result <- aux;
    return (result);
  }
}.

