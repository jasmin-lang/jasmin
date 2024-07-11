require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (buffer:W64.t) : unit = {
    var aux: int;
    
    var j:int;
    var i:int;
    
    i <- 0;
    while (i < 4) {
      aux <- (1 `<<` i);
      j <- 0;
      while (j < aux) {
        Glob.mem <- storeW8 Glob.mem (W64.to_uint (buffer + (W64.of_int ((16 * i) + j)))) ((W8.of_int 1));
        j <- j + 1;
      }
      i <- i + 1;
    }
    return ();
  }
}.

