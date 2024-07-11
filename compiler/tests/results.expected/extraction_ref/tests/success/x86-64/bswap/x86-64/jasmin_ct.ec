require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    var c:W32.t;
    var b:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- BSWAP_32 b;
    c <- aux;
    return (c);
  }
  
  proc g (p:W64.t) : unit = {
    var aux: W64.t;
    
    var a:W64.t;
    var b:W64.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- BSWAP_64 a;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 8)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) (aux);
    return ();
  }
}.

