require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_vpalignr_128 (cp:W64.t, ap:W64.t, bp:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (ap + (W64.of_int 0))));
    b <- (loadW128 Glob.mem (W64.to_uint (bp + (W64.of_int 0))));
    c <- VPALIGNR_128 a b (W8.of_int 8);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (cp + (W64.of_int 0))) (c);
    return ();
  }
  
  proc test_vpalignr_128_1 (cp:W64.t, ap:W64.t, bp:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (ap + (W64.of_int 0))));
    b <- (loadW128 Glob.mem (W64.to_uint (bp + (W64.of_int 0))));
    c <- VPALIGNR_128 a b (W8.of_int 8);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (cp + (W64.of_int 0))) (c);
    return ();
  }
  
  proc test_vpalignr_256 (cp:W64.t, ap:W64.t, bp:W64.t) : unit = {
    
    var a:W256.t;
    var b:W256.t;
    var c:W256.t;
    
    a <- (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int 0))));
    b <- (loadW256 Glob.mem (W64.to_uint (bp + (W64.of_int 0))));
    c <- VPALIGNR_256 a b (W8.of_int 8);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (cp + (W64.of_int 0))) (c);
    return ();
  }
}.

