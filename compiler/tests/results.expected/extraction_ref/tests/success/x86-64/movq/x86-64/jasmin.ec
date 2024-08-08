require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray32 WArray64.



module M = {
  proc test_movd_to_xmm (e:W32.t, r:W64.t, p:W64.t) : W128.t = {
    
    var x:W128.t;
    var y:W128.t;
    
    x <- MOVD_32 e;
    y <- MOVD_64 r;
    x <- (x `^` y);
    y <- MOVD_32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- (x `^` y);
    y <- MOVD_64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- (x `^` y);
    return (x);
  }
  
  proc test_movd_from_xmm (p:W64.t, x:W128.t, y:W256.t) : W32.t = {
    
    var e:W32.t;
    var f:W32.t;
    var r:W64.t;
    var s:W64.t;
    
    e <- MOVV_32 (truncateu32 x);
    f <- MOVV_32 (truncateu32 y);
    e <- (e `^` f);
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))) (MOVV_32 (truncateu32 x));
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 8))) (MOVV_32 (truncateu32 y));
    r <- MOVV_64 (truncateu64 x);
    s <- MOVV_64 (truncateu64 y);
    r <- (r `^` s);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 16))) (MOVV_64 (truncateu64 x));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 24))) (MOVV_64 (truncateu64 y));
    e <- (e `^` (truncateu32 r));
    return (e);
  }
  
  proc test_vmov_to_xmm (e:W32.t, r:W64.t, p:W64.t) : unit = {
    
    var x:W128.t Array2.t;
    var y:W256.t Array2.t;
    x <- witness;
    y <- witness;
    x.[0] <- VMOV_32 e;
    y.[0] <- zeroextu256(VMOV_32 e);
    x.[1] <- VMOV_32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y.[1] <- zeroextu256(VMOV_32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0)))));
    x.[0] <- (x.[0] `^` x.[1]);
    y.[0] <- (y.[0] `^` y.[1]);
    x.[1] <- VMOV_64 r;
    y.[1] <- zeroextu256(VMOV_64 r);
    x.[0] <- (x.[0] `^` x.[1]);
    y.[0] <- (y.[0] `^` y.[1]);
    x.[1] <- VMOV_64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y.[1] <- zeroextu256(VMOV_64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0)))));
    x.[0] <- (x.[0] `^` x.[1]);
    y.[0] <- (y.[0] `^` y.[1]);
    x.[0] <- (x.[0] `^` (truncateu128 y.[0]));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x.[0]);
    return ();
  }
}.

