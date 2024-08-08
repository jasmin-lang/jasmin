require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_vpmovsx_reg (p:W64.t, a:W128.t, b:W256.t) : W128.t = {
    
    var c:W128.t;
    var d:W256.t;
    
    a <- VPMOVSX_8u8_8u16 (truncateu64 a);
    c <- VPMOVSX_8u8_8u16 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVSX_16u8_16u16 (truncateu128 b);
    d <- VPMOVSX_16u8_16u16 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVSX_4u8_4u32 (truncateu32 a);
    c <- VPMOVSX_4u8_4u32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVSX_8u8_8u32 (truncateu64 b);
    d <- VPMOVSX_8u8_8u32 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVSX_2u8_2u64 (truncateu16 a);
    c <- VPMOVSX_2u8_2u64 (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVSX_4u8_4u64 (truncateu32 b);
    d <- VPMOVSX_4u8_4u64 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVSX_4u16_4u32 (truncateu64 a);
    c <- VPMOVSX_4u16_4u32 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVSX_8u16_8u32 (truncateu128 b);
    d <- VPMOVSX_8u16_8u32 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVSX_2u16_2u64 (truncateu32 a);
    c <- VPMOVSX_2u16_2u64 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVSX_4u16_4u64 (truncateu64 b);
    d <- VPMOVSX_4u16_4u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVSX_2u32_2u64 (truncateu64 a);
    c <- VPMOVSX_2u32_2u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVSX_4u32_4u64 (truncateu128 b);
    d <- VPMOVSX_4u32_4u64 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- (a `|` (truncateu128 b));
    return (a);
  }
  
  proc test_vpmovzx_reg (p:W64.t, a:W128.t, b:W256.t) : W128.t = {
    
    var c:W128.t;
    var d:W256.t;
    
    a <- VPMOVZX_8u8_8u16 (truncateu64 a);
    c <- VPMOVZX_8u8_8u16 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVZX_16u8_16u16 (truncateu128 b);
    d <- VPMOVZX_16u8_16u16 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVZX_4u8_4u32 (truncateu32 a);
    c <- VPMOVZX_4u8_4u32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVZX_8u8_8u32 (truncateu64 b);
    d <- VPMOVZX_8u8_8u32 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVZX_2u8_2u64 (truncateu16 a);
    c <- VPMOVZX_2u8_2u64 (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVZX_4u8_4u64 (truncateu32 b);
    d <- VPMOVZX_4u8_4u64 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVZX_4u16_4u32 (truncateu64 a);
    c <- VPMOVZX_4u16_4u32 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVZX_8u16_8u32 (truncateu128 b);
    d <- VPMOVZX_8u16_8u32 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVZX_2u16_2u64 (truncateu32 a);
    c <- VPMOVZX_2u16_2u64 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVZX_4u16_4u64 (truncateu64 b);
    d <- VPMOVZX_4u16_4u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- VPMOVZX_2u32_2u64 (truncateu64 a);
    c <- VPMOVZX_2u32_2u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- (a `|` c);
    b <- VPMOVZX_4u32_4u64 (truncateu128 b);
    d <- VPMOVZX_4u32_4u64 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (b `|` d);
    a <- (a `|` (truncateu128 b));
    return (a);
  }
}.

