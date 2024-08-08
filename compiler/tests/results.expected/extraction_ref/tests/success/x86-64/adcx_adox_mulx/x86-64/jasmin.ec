require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc adcx64 (x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    var of_0:bool;
    var cf:bool;
    var sf:bool;
    var pf:bool;
    var zf:bool;
    var aux:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    (of_0, cf, sf, pf, zf, x) <- ADD_64 x y;
    (cf, x) <- ADCX_64 x y cf;
    (of_0, x) <- ADOX_64 x y of_0;
    aux <- y;
    (hi, lo) <- MULX_64 aux x;
    r <- (hi + lo);
    return (r);
  }
  
  proc adcx32 (x:W32.t, y:W32.t) : W32.t = {
    
    var r:W32.t;
    var of_0:bool;
    var cf:bool;
    var sf:bool;
    var pf:bool;
    var zf:bool;
    var aux:W32.t;
    var hi:W32.t;
    var lo:W32.t;
    
    (of_0, cf, sf, pf, zf, x) <- ADD_32 x y;
    (cf, x) <- ADCX_32 x y cf;
    (of_0, x) <- ADOX_32 x y of_0;
    aux <- y;
    (hi, lo) <- MULX_32 aux x;
    r <- (hi + lo);
    return (r);
  }
}.

