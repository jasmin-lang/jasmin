require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_imm (x:W64.t) : W64.t = {
    
    var y:W64.t;
    var g:W64.t;
    
    g <- (W64.of_int 42);
    y <- x;
    y <- (y + g);
    return (y);
  }
}.

