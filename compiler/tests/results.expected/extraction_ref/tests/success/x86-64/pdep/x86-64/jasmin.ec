require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_pdep32 (tmp:W64.t) : unit = {
    
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    
    a <- (W32.of_int 255);
    b <- (W32.of_int 2);
    c <- PDEP_32 a b;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (c);
    return ();
  }
  
  proc test_pdep64 (tmp:W64.t) : unit = {
    
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    
    a <- (W64.of_int 255);
    b <- (W64.of_int 2);
    c <- PDEP_64 a b;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (c);
    return ();
  }
}.

