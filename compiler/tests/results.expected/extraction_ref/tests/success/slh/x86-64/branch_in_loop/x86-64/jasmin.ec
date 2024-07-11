require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc branch_in_loop (p:W64.t) : unit = {
    var aux: int;
    
    var msf:W64.t;
    var i:int;
    
    msf <- init_msf ;
    i <- 0;
    while (i < 10) {
      if ((i < 5)) {
        msf <- update_msf (i < 5) msf;
        p <- protect_64 p msf;
        Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int i))) ((W64.of_int i));
      } else {
        msf <- update_msf (! (i < 5)) msf;
      }
      i <- i + 1;
    }
    return ();
  }
}.

