require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_pext32 (tmp:W64.t) : unit = {
    var aux: W32.t;
    
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 255);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 2);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- PEXT_32 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_pext64 (tmp:W64.t) : unit = {
    var aux: W64.t;
    
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 255);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 2);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- PEXT_64 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux);
    return ();
  }
}.

