require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (r1:W64.t) : W64.t = {
    
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    
    r1 <- (W64.of_int 0);
    ( _0,  _1,  _2,  _3,  _4, r1) <- set0_64 ;
    return (r1);
  }
}.

