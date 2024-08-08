require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (y:W64.t) : unit = {
    
    var x:W64.t;
    
    x <- MOV_64 y;
    x <- (W64.of_int 1);
    x <- ((x = (W64.of_int 0)) ? y : x);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (x);
    return ();
  }
}.

