require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var y:W64.t;
    var  _0:W64.t;
    
    r <- (W64.of_int 0);
    y <- (W64.of_int 1);
    ( _0, y) <- mulu_64 y x;
    y <- r;
    r <- x;
    return (r);
  }
  
  proc g (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var one:W64.t;
    var cf:bool;
    
    r <- (W64.of_int 0);
    one <- (W64.of_int 1);
    
    while ((x \ult (W64.of_int 12))) {
      (cf, x) <- adc_64 x one false;
      r <- ((! cf) ? one : r);
    }
    return (r);
  }
}.

