require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc aes_test (p:W64.t) : W64.t = {
    
    var r:W64.t;
    var x1:W128.t;
    var x2:W128.t;
    var x3:W128.t;
    
    x1 <- set0_128 ;
    x2 <- set0_128 ;
    x1 <- AESENC x1 x2;
    x1 <- AESENC x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x1);
    x3 <- VAESENC_128 x1 x2;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x3);
    x3 <- VAESENC_128 x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x3);
    x1 <- AESDEC x1 x2;
    x1 <- AESDEC x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x1);
    x3 <- VAESDEC_128 x1 x2;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x3);
    x3 <- VAESDEC_128 x1 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x3);
    x1 <- AESIMC x1;
    x1 <- VAESIMC x1;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x1);
    x1 <- AESIMC (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x1 <- VAESIMC (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x1);
    x3 <- AESKEYGENASSIST x1 (W8.of_int 5);
    x3 <- AESKEYGENASSIST x3 (W8.of_int 4);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x3);
    x1 <- AESKEYGENASSIST (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0)))) (W8.of_int 3);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x1);
    x3 <- VAESKEYGENASSIST x1 (W8.of_int 1);
    x3 <- VAESKEYGENASSIST x3 (W8.of_int 2);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x3);
    x1 <- VAESKEYGENASSIST (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0)))) (W8.of_int 0);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x1);
    r <- (W64.of_int 0);
    return (r);
  }
  
  proc test_vaes (p:W64.t) : unit = {
    
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- VAESENC_256 x (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    z <- VAESENC_256 y x;
    x <- VAESENCLAST_256 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    y <- VAESENCLAST_256 x y;
    z <- VAESDEC_256 y (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    x <- VAESDEC_256 z y;
    y <- VAESDECLAST_256 x (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    z <- VAESDECLAST_256 y x;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (z);
    return ();
  }
}.

