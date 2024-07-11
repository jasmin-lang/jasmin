require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_vpavgb (out:W64.t, in_0:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W256.t;
    var e:W256.t;
    var f:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    b <- VPAVG_16u8 a (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 16))));
    c <- VPAVG_16u8 a b;
    d <- zeroextu256(VPAVG_16u8 a c);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (out + (W64.of_int 0))) (c);
    e <- VPAVG_32u8 d (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 32))));
    f <- VPAVG_32u8 d e;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (out + (W64.of_int 32))) (f);
    return ();
  }
  
  proc test_vpavgw (out:W64.t, in_0:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W256.t;
    var e:W256.t;
    var f:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    b <- VPAVG_8u16 a (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 16))));
    c <- VPAVG_8u16 a b;
    d <- zeroextu256(VPAVG_8u16 a c);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (out + (W64.of_int 0))) (c);
    e <- VPAVG_16u16 d (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 32))));
    f <- VPAVG_16u16 d e;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (out + (W64.of_int 32))) (f);
    return ();
  }
}.

