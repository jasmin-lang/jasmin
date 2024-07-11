require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t) : W64.t = {
    
    var y:W64.t;
    var cf:bool;
    var  _0:bool;
    
    y <- x;
    cf <- BT_64 x (W64.of_int 4);
    ( _0, y) <- adc_64 y x cf;
    return (y);
  }
}.

