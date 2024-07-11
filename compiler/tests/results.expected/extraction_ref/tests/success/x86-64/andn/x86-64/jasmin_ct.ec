require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f32 (x:W32.t, y:W32.t) : W32.t = {
    var aux: W32.t;
    
    var z:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((invw x) `&` y);
    z <- aux;
    return (z);
  }
  
  proc f64 (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((invw x) `&` y);
    z <- aux;
    return (z);
  }
  
  proc m32 (x:W32.t, p:W64.t) : W32.t = {
    var aux: W32.t;
    
    var z:W32.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- ((invw x) `&` (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0)))));
    z <- aux;
    return (z);
  }
  
  proc m64 (x:W64.t, p:W64.t) : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- ((invw x) `&` (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0)))));
    z <- aux;
    return (z);
  }
}.

