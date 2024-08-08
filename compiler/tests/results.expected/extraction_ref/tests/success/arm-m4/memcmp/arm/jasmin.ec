require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc memcmp (p:W32.t, q:W32.t, n:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var i:W32.t;
    var a:W32.t;
    var b:W32.t;
    
    res_0 <- (W32.of_int 1);
    i <- (W32.of_int 0);
    
    while ((i \ult n)) {
      a <- (loadW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))));
      b <- (loadW32 Glob.mem (W32.to_uint (q + (W32.of_int 0))));
      if ((a <> b)) {
        res_0 <- (W32.of_int 0);
      } else {
        
      }
      p <- (p + (W32.of_int 4));
      q <- (q + (W32.of_int 4));
      i <- (i + (W32.of_int 1));
    }
    res_0 <- res_0;
    return (res_0);
  }
}.

