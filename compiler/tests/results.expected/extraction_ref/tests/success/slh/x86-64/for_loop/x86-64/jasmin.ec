require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (p:W64.t) : unit = {
    var aux: int;
    
    var msf:W64.t;
    var i:int;
    
    msf <- init_msf ;
    i <- 0;
    while (i < 10) {
      msf <- update_msf (i < 10) msf;
      p <- protect_64 p msf;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int i))) ((W64.of_int i));
      i <- i + 1;
    }
    return ();
  }
}.

