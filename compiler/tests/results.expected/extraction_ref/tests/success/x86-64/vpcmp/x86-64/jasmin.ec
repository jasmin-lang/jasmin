require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_vpcmpgt (tmp:W64.t) : unit = {
    
    var y:W256.t;
    var x:W256.t;
    var z:W256.t;
    var i:W128.t;
    var j:W128.t;
    var k:W128.t;
    
    y <- set0_256 ;
    x <- set0_256 ;
    z <- VPCMPGT_32u8 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (z);
    i <- set0_128 ;
    j <- set0_128 ;
    k <- VPCMPGT_8u16 i j;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (tmp + (W64.of_int 32))) (k);
    z <- VPCMPGT_8u32 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 64))) (z);
    j <- VPCMPGT_2u64 i (loadW128 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))));
    k <- VPCMPGT_2u64 i j;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (k);
    y <- VPCMPGT_4u64 x (loadW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))));
    z <- VPCMPGT_4u64 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (z);
    return ();
  }
  
  proc test_vpcmpeq (p:W64.t) : unit = {
    
    var i:W128.t;
    var j:W128.t;
    var k:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    i <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    j <- VPCMPEQ_16u8 i (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    k <- VPCMPEQ_16u8 i j;
    i <- VPCMPEQ_8u16 k (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    k <- VPCMPEQ_8u16 i j;
    j <- VPCMPEQ_4u32 k (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    k <- VPCMPEQ_4u32 i j;
    j <- VPCMPEQ_2u64 k (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    k <- VPCMPEQ_2u64 i j;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (k);
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- VPCMPEQ_32u8 x (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    z <- VPCMPEQ_32u8 x y;
    x <- VPCMPEQ_16u16 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    z <- VPCMPEQ_16u16 x y;
    y <- VPCMPEQ_8u32 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    z <- VPCMPEQ_8u32 x y;
    y <- VPCMPEQ_4u64 z (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    z <- VPCMPEQ_4u64 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (z);
    return ();
  }
}.

