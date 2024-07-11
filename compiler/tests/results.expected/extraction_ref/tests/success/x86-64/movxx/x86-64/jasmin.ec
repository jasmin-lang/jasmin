require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_movsx (x:W64.t, y:W64.t) : unit = {
    
    var a:W16.t;
    var b:W32.t;
    var c:W64.t;
    
    a <- MOVSX_u16s8 (truncateu8 x);
    b <- MOVSX_u32s16 a;
    b <- MOVSX_u32s8 (truncateu8 b);
    c <- MOVSX_u64s32 b;
    c <- MOVSX_u64s16 (truncateu16 c);
    c <- MOVSX_u64s8 (truncateu8 c);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (c);
    a <- MOVSX_u16s8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (a);
    b <- MOVSX_u32s16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (b);
    b <- MOVSX_u32s8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (b);
    c <- MOVSX_u64s32 (loadW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (c);
    c <- MOVSX_u64s16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (c);
    c <- MOVSX_u64s8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (c);
    return ();
  }
  
  proc test_movzx (x:W64.t, y:W64.t) : unit = {
    
    var a:W16.t;
    var b:W32.t;
    var c:W64.t;
    
    a <- MOVZX_u16u8 (truncateu8 x);
    b <- MOVZX_u32u16 a;
    b <- MOVZX_u32u8 (truncateu8 b);
    c <- MOVZX_u64u16 (truncateu16 b);
    c <- MOVZX_u64u8 (truncateu8 c);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (c);
    a <- MOVZX_u16u8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (a);
    b <- MOVZX_u32u16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (b);
    b <- MOVZX_u32u8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (b);
    c <- MOVZX_u64u16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (c);
    c <- MOVZX_u64u8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (c);
    return ();
  }
}.

