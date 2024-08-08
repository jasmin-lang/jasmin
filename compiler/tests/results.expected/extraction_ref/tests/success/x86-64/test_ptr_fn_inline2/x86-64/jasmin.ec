require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc init () : W64.t Array1.t = {
    
    var h:W64.t Array1.t;
    h <- witness;
    h.[0] <- (W64.of_int 0);
    return (h);
  }
  
  proc foo (t:W64.t Array1.t) : W64.t Array1.t = {
    
    
    
    t.[0] <- (W64.of_int 1);
    return (t);
  }
  
  proc main () : W64.t = {
    
    var r:W64.t;
    var h:W64.t Array1.t;
    var t:W64.t Array1.t;
    h <- witness;
    t <- witness;
    h <@ init ();
    t <@ foo (h);
    r <- t.[0];
    return (r);
  }
}.

