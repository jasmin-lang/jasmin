require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc exp (e:W64.t) : W64.t = {
    
    var m:W64.t;
    var c:bool;
    
    m <- (W64.of_int 1);
    c <- (e <> (W64.of_int 0));
    m <- (c ? e : m);
    return (m);
  }
}.

