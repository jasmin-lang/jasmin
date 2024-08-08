require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array1.
require import WArray8.



module M = {
  proc f (a:W64.t Array1.t, x:W64.t) : W64.t Array1.t * W64.t = {
    
    var s:W64.t Array1.t;
    s <- witness;
    s <- a;
    a <- s;
    return (a, x);
  }
  
  proc main () : unit = {
    
    var x:W64.t;
    var a:W64.t Array1.t;
    var  _0:W64.t Array1.t;
    var  _1:W64.t;
     _0 <- witness;
    a <- witness;
    x <- (W64.of_int 0);
    a.[0] <- (W64.of_int 0);
    if (false) {
      ( _0,  _1) <@ f (a, x);
    } else {
      
    }
    return ();
  }
}.

