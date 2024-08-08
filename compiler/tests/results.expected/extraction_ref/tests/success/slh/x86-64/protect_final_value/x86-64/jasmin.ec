require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc protect_final_value (p:W64.t) : W64.t = {
    
    var sum:W64.t;
    var msf:W64.t;
    var i:W64.t;
    var b:bool;
    var temp:W64.t;
    
    msf <- init_msf ;
    sum <- (W64.of_int 0);
    i <- (W64.of_int 0);
    b <- (i \ult (W64.of_int 10));
    b <- (i \ult (W64.of_int 10));
    while (b) {
      msf <- update_msf b msf;
      temp <- (loadW64 Glob.mem (W64.to_uint (p + i)));
      sum <- (sum + temp);
      i <- (i + (W64.of_int 1));
      b <- (i \ult (W64.of_int 10));
    }
    msf <- update_msf (! b) msf;
    sum <- protect_64 sum msf;
    return (sum);
  }
}.

