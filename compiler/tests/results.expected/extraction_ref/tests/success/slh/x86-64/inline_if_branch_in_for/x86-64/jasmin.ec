require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc branch_in_loop (p:W64.t) : W64.t = {
    var aux: int;
    
    var x:W64.t;
    var msf:W64.t;
    var i:int;
    
    msf <- init_msf ;
    x <- (W64.of_int 0);
    i <- 0;
    while (i < 10) {
      if ((i < 5)) {
        Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int i))) ((W64.of_int i));
        x <- (x + (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int i)))));
      } else {
        Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int i))) ((W64.of_int 10));
        x <- (x + (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int i)))));
      }
      i <- i + 1;
    }
    return (x);
  }
}.

