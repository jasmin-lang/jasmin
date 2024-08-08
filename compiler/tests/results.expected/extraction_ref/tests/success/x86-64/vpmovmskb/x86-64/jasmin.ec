require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_pmovmskb (tmp:W64.t) : unit = {
    
    var x:W128.t;
    var y:W256.t;
    var a:W32.t;
    var b:W64.t;
    
    x <- set0_128 ;
    y <- set0_256 ;
    a <- VPMOVMSKB_u128u32 x;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (a);
    b <- VPMOVMSKB_u128u64 x;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (b);
    a <- VPMOVMSKB_u256u32 y;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (a);
    b <- VPMOVMSKB_u256u64 y;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (b);
    return ();
  }
}.

