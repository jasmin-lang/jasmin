require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray32 WArray64.



module M = {
  var leakages : leakages_t
  
  proc test_movd_to_xmm (e:W32.t, r:W64.t, p:W64.t) : W128.t = {
    var aux: W128.t;
    
    var x:W128.t;
    var y:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVD_32 e;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVD_64 r;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- MOVD_32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- MOVD_64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    return (x);
  }
  
  proc test_movd_from_xmm (p:W64.t, x:W128.t, y:W256.t) : W32.t = {
    var aux: W32.t;
    var aux_0: W64.t;
    
    var e:W32.t;
    var f:W32.t;
    var r:W64.t;
    var s:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVV_32 (truncateu32 x);
    e <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVV_32 (truncateu32 y);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (e `^` f);
    e <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVV_32 (truncateu32 x);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 4)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVV_32 (truncateu32 y);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 8)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 8))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVV_64 (truncateu64 x);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVV_64 (truncateu64 y);
    s <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (r `^` s);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVV_64 (truncateu64 x);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 16)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 16))) (aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOVV_64 (truncateu64 y);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 24)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 24))) (aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (e `^` (truncateu32 r));
    e <- aux;
    return (e);
  }
  
  proc test_vmov_to_xmm (e:W32.t, r:W64.t, p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var x:W128.t Array2.t;
    var y:W256.t Array2.t;
    x <- witness;
    y <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOV_32 e;
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOV_32 e;
    leakages <- LeakAddr([0]) :: leakages;
    y.[0] <- zeroextu256(aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VMOV_32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VMOV_32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    leakages <- LeakAddr([1]) :: leakages;
    y.[1] <- zeroextu256(aux);
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux <- (x.[0] `^` x.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux_0 <- (y.[0] `^` y.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    y.[0] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOV_64 r;
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOV_64 r;
    leakages <- LeakAddr([1]) :: leakages;
    y.[1] <- zeroextu256(aux);
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux <- (x.[0] `^` x.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux_0 <- (y.[0] `^` y.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    y.[0] <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VMOV_64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VMOV_64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    leakages <- LeakAddr([1]) :: leakages;
    y.[1] <- zeroextu256(aux);
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux <- (x.[0] `^` x.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux_0 <- (y.[0] `^` y.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    y.[0] <- aux_0;
    leakages <- LeakAddr([0; 0]) :: leakages;
    aux <- (x.[0] `^` (truncateu128 y.[0]));
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
}.

