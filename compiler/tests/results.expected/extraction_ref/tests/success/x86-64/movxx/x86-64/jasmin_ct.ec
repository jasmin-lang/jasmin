require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_movsx (x:W64.t, y:W64.t) : unit = {
    var aux: W16.t;
    var aux_0: W32.t;
    var aux_1: W64.t;
    
    var a:W16.t;
    var b:W32.t;
    var c:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVSX_u16s8 (truncateu8 x);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVSX_u32s16 a;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVSX_u32s8 (truncateu8 b);
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- MOVSX_u64s32 b;
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- MOVSX_u64s16 (truncateu16 c);
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- MOVSX_u64s8 (truncateu8 c);
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- c;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux <- MOVSX_u16s8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_0 <- MOVSX_u32s16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_0 <- MOVSX_u32s8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_1 <- MOVSX_u64s32 (loadW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- c;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_1 <- MOVSX_u64s16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- c;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_1 <- MOVSX_u64s8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- c;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_1);
    return ();
  }
  
  proc test_movzx (x:W64.t, y:W64.t) : unit = {
    var aux: W16.t;
    var aux_0: W32.t;
    var aux_1: W64.t;
    
    var a:W16.t;
    var b:W32.t;
    var c:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVZX_u16u8 (truncateu8 x);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVZX_u32u16 a;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVZX_u32u8 (truncateu8 b);
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- MOVZX_u64u16 (truncateu16 b);
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- MOVZX_u64u8 (truncateu8 c);
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- c;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux <- MOVZX_u16u8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_0 <- MOVZX_u32u16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_0 <- MOVZX_u32u8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- b;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_0);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_1 <- MOVZX_u64u16 (loadW16 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- c;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux_1 <- MOVZX_u64u8 (loadW8 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- c;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (y + (W64.of_int 0))) (aux_1);
    return ();
  }
}.

