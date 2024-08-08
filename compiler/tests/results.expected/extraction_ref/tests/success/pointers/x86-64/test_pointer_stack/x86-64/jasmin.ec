require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc incr (t:W64.t Array1.t) : W64.t Array1.t = {
    
    
    
    t.[0] <- (t.[0] + (W64.of_int 1));
    return (t);
  }
  
  proc sum (a:W64.t Array1.t, b:W64.t Array1.t) : W64.t Array1.t = {
    
    var d:W64.t Array1.t;
    var aux:W64.t;
    d <- witness;
    aux <- a.[0];
    aux <- (aux + b.[0]);
    d.[0] <- aux;
    return (d);
  }
  
  proc test () : W64.t = {
    
    var res_0:W64.t;
    var a1:W64.t Array1.t;
    var a2:W64.t Array1.t;
    var a3:W64.t Array1.t;
    a1 <- witness;
    a2 <- witness;
    a3 <- witness;
    a1.[0] <- (W64.of_int 1);
    a2.[0] <- (W64.of_int 1);
    a3 <@ sum (a1, a2);
    a3 <@ incr (a3);
    res_0 <- a3.[0];
    return (res_0);
  }
}.

