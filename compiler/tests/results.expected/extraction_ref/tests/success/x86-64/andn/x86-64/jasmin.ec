require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f32 (x:W32.t, y:W32.t) : W32.t = {
    
    var z:W32.t;
    
    z <- ((invw x) `&` y);
    return (z);
  }
  
  proc f64 (x:W64.t, y:W64.t) : W64.t = {
    
    var z:W64.t;
    
    z <- ((invw x) `&` y);
    return (z);
  }
  
  proc m32 (x:W32.t, p:W64.t) : W32.t = {
    
    var z:W32.t;
    
    z <- ((invw x) `&` (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0)))));
    return (z);
  }
  
  proc m64 (x:W64.t, p:W64.t) : W64.t = {
    
    var z:W64.t;
    
    z <- ((invw x) `&` (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0)))));
    return (z);
  }
}.

