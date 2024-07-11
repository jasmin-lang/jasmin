require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray8.



module M = {
  proc test_sum_u8 (ptr_:W64.t, len:W64.t) : W8.t = {
    
    var r:W8.t;
    var off:W64.t;
    
    r <- (W8.of_int 0);
    off <- (W64.of_int 0);
    
    while ((off \ult len)) {
      r <- (r + (loadW8 Glob.mem (W64.to_uint (ptr_ + off))));
      off <- (off + (W64.of_int 1));
    }
    return (r);
  }
  
  proc test_xor_u16 (ptr_:W64.t, len:W64.t) : W16.t = {
    
    var r:W16.t;
    var off:W64.t;
    
    r <- (W16.of_int 0);
    off <- (W64.of_int 0);
    
    while ((off \ult len)) {
      r <- (r `^` (loadW16 Glob.mem (W64.to_uint (ptr_ + (off * (W64.of_int 2))))));
      off <- (off + (W64.of_int 1));
    }
    return (r);
  }
  
  proc test_swap_u32 (ptr_:W64.t) : W64.t = {
    var aux: int;
    
    var z:W64.t;
    var i:int;
    var w:W32.t Array2.t;
    w <- witness;
    i <- 0;
    while (i < 2) {
      w.[i] <- (loadW32 Glob.mem (W64.to_uint (ptr_ + (W64.of_int (i * 4)))));
      i <- i + 1;
    }
    i <- 0;
    while (i < 2) {
      Glob.mem <- storeW32 Glob.mem (W64.to_uint (ptr_ + (W64.of_int ((1 - i) * 4)))) (w.[i]);
      i <- i + 1;
    }
    z <- (W64.of_int 0);
    return (z);
  }
  
  proc test_u128 (ptr_:W64.t) : W64.t = {
    
    var r:W64.t;
    var t:W128.t;
    
    r <- (W64.of_int 0);
    t <- (loadW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int (16 * 0)))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int (16 * 1)))) (t);
    return (r);
  }
}.

