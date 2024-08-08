require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test () : W64.t = {
    
    var x2:W64.t;
    var x1:W64.t;
    var  _0:bool;
    
    x1 <- (W64.of_int 0);
    x2 <- (W64.of_int 1);
    ( _0, x1) <- adc_64 x1 x2 false;
    x2 <- LEA_64 (x1 + (W64.of_int 1));
    x2 <- (x2 + x1);
    return (x2);
  }
}.

