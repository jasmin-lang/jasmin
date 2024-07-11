require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_zeroext (a:W8.t) : W32.t = {
    var aux: W16.t;
    var aux_0: W32.t;
    var aux_1: W64.t;
    
    var d:W32.t;
    var b:W16.t;
    var c:W32.t;
    var e:W64.t;
    var f:W64.t;
    var g:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu16 a);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (zeroextu32 a);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (zeroextu32 b);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (zeroextu64 a);
    e <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (zeroextu64 b);
    f <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (zeroextu64 c);
    g <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (f + e);
    f <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (g + f);
    g <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (d + (truncateu32 g));
    d <- aux_0;
    return (d);
  }
  
  proc test_signext (a:W8.t) : W32.t = {
    var aux: W16.t;
    var aux_0: W32.t;
    var aux_1: W64.t;
    
    var d:W32.t;
    var b:W16.t;
    var c:W32.t;
    var e:W64.t;
    var f:W64.t;
    var g:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (sigextu16 a);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (sigextu32 a);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (sigextu32 b);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (sigextu64 a);
    e <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (sigextu64 b);
    f <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (sigextu64 c);
    g <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (f + e);
    f <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (g + f);
    g <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (d + (truncateu32 g));
    d <- aux_0;
    return (d);
  }
  
  proc test_u128 (ptr_:W64.t, v:W64.t, w:W32.t) : unit = {
    var aux: W128.t;
    
    var x:W128.t;
    var y:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu128 v);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu128 w);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOV_64 v;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOV_32 w;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (ptr_ + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_u256 (ptr_:W64.t, v:W64.t, w:W32.t) : unit = {
    var aux_0: W128.t;
    var aux: W256.t;
    
    var x:W256.t;
    var y:W256.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu256 v);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu256 w);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (ptr_ + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int 0))) ((truncateu128 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (ptr_ + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (ptr_ + (W64.of_int 32))) (aux);
    return ();
  }
  
  proc test_imm (p:W64.t) : unit = {
    var aux: W8.t;
    var aux_0: W16.t;
    var aux_1: W32.t;
    var aux_2: W64.t;
    
    var a:W8.t;
    var b:W16.t;
    var c:W32.t;
    var d:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int 255);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (sigextu16 a);
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (sigextu32 b);
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (sigextu64 c);
    d <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- d;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_2);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int 255);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (zeroextu16 a);
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (zeroextu32 b);
    c <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (zeroextu64 c);
    d <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- d;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 8)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) (aux_2);
    return ();
  }
  
  proc test_truncate (y:W256.t) : W32.t = {
    var aux_2: W32.t;
    var aux_1: W64.t;
    var aux: W128.t;
    var aux_0: W256.t;
    
    var f:W32.t;
    var x:W128.t;
    var r:W64.t;
    var s:W64.t;
    var e:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    x <- (truncateu128 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    r <- (truncateu64 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    s <- (truncateu64 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (s `^` r);
    s <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    e <- (truncateu32 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    f <- (truncateu32 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (f `^` e);
    f <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (f `^` (truncateu32 s));
    f <- aux_2;
    return (f);
  }
  
  proc test_avx_to_mem (p:W64.t, y:W256.t) : unit = {
    var aux_1: W32.t;
    var aux_2: W64.t;
    var aux: W128.t;
    var aux_0: W256.t;
    
    var x:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    x <- (truncateu128 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))) ((truncateu32 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 4)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))) ((truncateu32 aux_0));
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 8)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) ((truncateu64 aux));
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 16)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 16))) ((truncateu64 aux_0));
    return ();
  }
}.

