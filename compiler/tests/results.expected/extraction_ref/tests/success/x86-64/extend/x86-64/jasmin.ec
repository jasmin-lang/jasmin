require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_zeroext (a:W8.t) : W32.t = {
    
    var d:W32.t;
    var b:W16.t;
    var c:W32.t;
    var e:W64.t;
    var f:W64.t;
    var g:W64.t;
    
    b <- (zeroextu16 a);
    c <- (zeroextu32 a);
    d <- (zeroextu32 b);
    e <- (zeroextu64 a);
    f <- (zeroextu64 b);
    g <- (zeroextu64 c);
    f <- (f + e);
    g <- (g + f);
    d <- (d + (truncateu32 g));
    return (d);
  }
  
  proc test_signext (a:W8.t) : W32.t = {
    
    var d:W32.t;
    var b:W16.t;
    var c:W32.t;
    var e:W64.t;
    var f:W64.t;
    var g:W64.t;
    
    b <- (sigextu16 a);
    c <- (sigextu32 a);
    d <- (sigextu32 b);
    e <- (sigextu64 a);
    f <- (sigextu64 b);
    g <- (sigextu64 c);
    f <- (f + e);
    g <- (g + f);
    d <- (d + (truncateu32 g));
    return (d);
  }
  
  proc test_u128 (ptr_:W64.t, v:W64.t, w:W32.t) : unit = {
    
    var x:W128.t;
    var y:W128.t;
    
    x <- (zeroextu128 v);
    y <- (zeroextu128 w);
    x <- (x `^` y);
    y <- VMOV_64 v;
    x <- (x `^` y);
    y <- VMOV_32 w;
    x <- (x `^` y);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int 0))) (x);
    return ();
  }
  
  proc test_u256 (ptr_:W64.t, v:W64.t, w:W32.t) : unit = {
    
    var x:W256.t;
    var y:W256.t;
    
    x <- set0_256 ;
    y <- (zeroextu256 v);
    x <- (x `^` y);
    y <- (zeroextu256 w);
    x <- (x `^` y);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (ptr_ + (W64.of_int 0))) ((truncateu128 x));
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (ptr_ + (W64.of_int 32))) (x);
    return ();
  }
  
  proc test_imm (p:W64.t) : unit = {
    
    var a:W8.t;
    var b:W16.t;
    var c:W32.t;
    var d:W64.t;
    
    a <- (W8.of_int 255);
    b <- (sigextu16 a);
    c <- (sigextu32 b);
    d <- (sigextu64 c);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (d);
    a <- (W8.of_int 255);
    b <- (zeroextu16 a);
    c <- (zeroextu32 b);
    d <- (zeroextu64 c);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) (d);
    return ();
  }
  
  proc test_truncate (y:W256.t) : W32.t = {
    
    var f:W32.t;
    var x:W128.t;
    var r:W64.t;
    var s:W64.t;
    var e:W32.t;
    
    x <- (truncateu128 y);
    r <- (truncateu64 y);
    s <- (truncateu64 x);
    s <- (s `^` r);
    e <- (truncateu32 y);
    f <- (truncateu32 x);
    f <- (f `^` e);
    f <- (f `^` (truncateu32 s));
    return (f);
  }
  
  proc test_avx_to_mem (p:W64.t, y:W256.t) : unit = {
    
    var x:W128.t;
    
    x <- (truncateu128 y);
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))) ((truncateu32 x));
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))) ((truncateu32 y));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) ((truncateu64 x));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 16))) ((truncateu64 y));
    return ();
  }
}.

