require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc read (ro:W64.t Array1.t) : W64.t = {
    
    var v:W64.t;
    
    v <- ro.[0];
    return (v);
  }
  
  proc write (arg:W64.t Array1.t) : W64.t Array1.t = {
    
    var x:W64.t;
    
    arg.[0] <- (W64.of_int 0);
    x <@ read (arg);
    arg.[0] <- x;
    return (arg);
  }
  
  proc test () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array1.t;
    var rw:W64.t Array1.t;
    rw <- witness;
    s <- witness;
    rw <- s;
    rw <@ write (rw);
    r <- rw.[0];
    return (r);
  }
}.

