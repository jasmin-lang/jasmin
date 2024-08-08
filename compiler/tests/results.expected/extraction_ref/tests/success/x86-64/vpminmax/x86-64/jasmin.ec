require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc minmax (inp:W64.t) : unit = {
    
    var x1:W128.t;
    var x2:W128.t;
    var y1:W256.t;
    var y2:W256.t;
    
    x1 <- (loadW128 Glob.mem (W64.to_uint (inp + (W64.of_int 0))));
    x2 <- (loadW128 Glob.mem (W64.to_uint (inp + (W64.of_int 16))));
    y1 <- (loadW256 Glob.mem (W64.to_uint (inp + (W64.of_int 0))));
    y2 <- (loadW256 Glob.mem (W64.to_uint (inp + (W64.of_int 32))));
    x1 <- VPMINS_4u32 x1 x2;
    x1 <- VPMINU_4u32 x1 x2;
    x1 <- VPMINS_8u16 x1 x2;
    x1 <- VPMINU_8u16 x1 x2;
    x1 <- VPMINS_16u8 x1 x2;
    x1 <- VPMINU_16u8 x1 x2;
    x1 <- VPMAXS_4u32 x1 x2;
    x1 <- VPMAXU_4u32 x1 x2;
    x1 <- VPMAXS_8u16 x1 x2;
    x1 <- VPMAXU_8u16 x1 x2;
    x1 <- VPMAXS_16u8 x1 x2;
    x1 <- VPMAXU_16u8 x1 x2;
    y1 <- VPMINS_8u32 y1 y2;
    y1 <- VPMINU_8u32 y1 y2;
    y1 <- VPMINS_16u16 y1 y2;
    y1 <- VPMINU_16u16 y1 y2;
    y1 <- VPMINS_32u8 y1 y2;
    y1 <- VPMINU_32u8 y1 y2;
    y1 <- VPMAXS_8u32 y1 y2;
    y1 <- VPMAXU_8u32 y1 y2;
    y1 <- VPMAXS_16u16 y1 y2;
    y1 <- VPMAXU_16u16 y1 y2;
    y1 <- VPMAXS_32u8 y1 y2;
    y1 <- VPMAXU_32u8 y1 y2;
    x1 <- VPMINS_4u32 x1 x2;
    x1 <- VPMINU_4u32 x1 x2;
    x1 <- VPMINS_8u16 x1 x2;
    x1 <- VPMINU_8u16 x1 x2;
    x1 <- VPMINS_16u8 x1 x2;
    x1 <- VPMINU_16u8 x1 x2;
    x1 <- VPMAXS_4u32 x1 x2;
    x1 <- VPMAXU_4u32 x1 x2;
    x1 <- VPMAXS_8u16 x1 x2;
    x1 <- VPMAXU_8u16 x1 x2;
    x1 <- VPMAXS_16u8 x1 x2;
    x1 <- VPMAXU_16u8 x1 x2;
    y1 <- VPMINS_8u32 y1 y2;
    y1 <- VPMINU_8u32 y1 y2;
    y1 <- VPMINS_16u16 y1 y2;
    y1 <- VPMINU_16u16 y1 y2;
    y1 <- VPMINS_32u8 y1 y2;
    y1 <- VPMINU_32u8 y1 y2;
    y1 <- VPMAXS_8u32 y1 y2;
    y1 <- VPMAXU_8u32 y1 y2;
    y1 <- VPMAXS_16u16 y1 y2;
    y1 <- VPMAXU_16u16 y1 y2;
    y1 <- VPMAXS_32u8 y1 y2;
    y1 <- VPMAXU_32u8 y1 y2;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (inp + (W64.of_int 0))) (x1);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (inp + (W64.of_int 0))) (y1);
    return ();
  }
}.

