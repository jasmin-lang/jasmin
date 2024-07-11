require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f () : unit = {
    var aux: W64.t;
    
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x <- aux;
    leakages <- LeakCond((x = (W64.of_int 0))) :: LeakAddr([]) :: leakages;
    if ((x = (W64.of_int 0))) {
      
    } else {
      
    }
    return ();
  }
  
  proc main (x:W64.t) : unit = {
    var aux: W64.t;
    
    var msf:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    f ();
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux);
    return ();
  }
}.

