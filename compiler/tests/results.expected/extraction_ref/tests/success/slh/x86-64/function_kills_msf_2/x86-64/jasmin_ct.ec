require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : unit = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc main (x:W64.t, r:W64.t) : W64.t = {
    var aux: W64.t;
    
    var ms:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    ms <- aux;
    leakages <- LeakAddr([]) :: leakages;
    f (x);
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 r ms;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
}.

