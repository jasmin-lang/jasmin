require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc test1 (x:W64.t) : W64.t = {
    
    var a:W64.t Array1.t;
    var b:W64.t Array1.t;
    a <- witness;
    b <- witness;
    a.[0] <- x;
    x <- (x + a.[0]);
    b.[0] <- x;
    x <- (x + b.[0]);
    return (x);
  }
  
  proc test2 (x:W64.t) : W64.t = {
    
    var b:W64.t Array1.t;
    var a:W64.t Array1.t;
    a <- witness;
    b <- witness;
    if ((x = (W64.of_int 1))) {
      a.[0] <- x;
      x <- (x + a.[0]);
      b.[0] <- x;
      x <- (x + b.[0]);
    } else {
      b.[0] <- x;
      x <- (x + b.[0]);
    }
    return (x);
  }
  
  proc test (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    r <@ test1 (r);
    r <@ test2 (r);
    return (r);
  }
}.

