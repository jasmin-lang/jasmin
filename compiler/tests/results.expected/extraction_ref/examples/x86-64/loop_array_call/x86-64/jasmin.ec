require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc reduce () : W64.t Array1.t = {
    
    var xa:W64.t Array1.t;
    xa <- witness;
    xa.[0] <- (W64.of_int 0);
    return (xa);
  }
  
  proc iterated_square (xa:W64.t Array1.t, n:W64.t) : W64.t Array1.t = {
    
    var cf:bool;
    
    xa <@ reduce ();
    (cf, n) <- sbb_64 n (W64.of_int 1) false;
    while ((! cf)) {
      xa <@ reduce ();
      (cf, n) <- sbb_64 n (W64.of_int 1) false;
    }
    return (xa);
  }
  
  proc iterated_square_export (xap:W64.t, n:W64.t) : unit = {
    
    var xa:W64.t Array1.t;
    var ns:W64.t;
    xa <- witness;
    xa.[0] <- (loadW64 Glob.mem (W64.to_uint (xap + (W64.of_int 0))));
    ns <- n;
    xa <@ iterated_square (xa, ns);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (xap + (W64.of_int 0))) (xa.[0]);
    return ();
  }
}.

