require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (a:W32.t) : W32.t = {
    
    var c:W32.t;
    var b:W32.t;
    
    b <- a;
    c <- BSWAP_32 b;
    return (c);
  }
  
  proc g (p:W64.t) : unit = {
    
    var a:W64.t;
    var b:W64.t;
    
    a <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- BSWAP_64 a;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) (b);
    return ();
  }
}.

