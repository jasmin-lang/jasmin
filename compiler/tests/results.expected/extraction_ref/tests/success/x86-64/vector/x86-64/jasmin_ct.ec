require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.

abbrev rotate24pattern = W128.of_int 16028905388486802350658220295983399425.


module M = {
  var leakages : leakages_t
  
  proc test_mem128 (p:W64.t) : unit = {
    var aux: W128.t;
    
    var r:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 0))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 1))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (aux);
    return ();
  }
  
  proc test_vmovdqa (p:W64.t) : unit = {
    var aux: W128.t;
    
    var r:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 0))))]) :: leakages;
    aux <- VMOVDQA_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOVDQA_128 r;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 1))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (aux);
    return ();
  }
  
  proc test_vmovdqu (p:W64.t) : unit = {
    var aux: W128.t;
    
    var r:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 0))))]) :: leakages;
    aux <- VMOVDQU_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOVDQU_128 r;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 1))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (aux);
    return ();
  }
  
  proc test_xor (p:W64.t) : unit = {
    var aux: W128.t;
    
    var r:W128.t;
    var s:W128.t;
    var t:W128.t;
    var u:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 0))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    r <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 1))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))));
    s <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 2))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 2)))));
    t <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 3))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 3)))));
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r `^` s);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r `&` t);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r `|` u);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 1))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (aux);
    return ();
  }
  
  proc test_add (p:W64.t) : unit = {
    var aux: W128.t;
    
    var r:W128.t;
    var s:W128.t;
    var u:W128.t;
    var t:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 0))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    r <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 1))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))));
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPADD_16u8 r s;
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPADD_8u16 r u;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPADD_4u32 s t;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPADD_2u64 t r;
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 1))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (aux);
    return ();
  }
  
  proc test_mul (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 16)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPMUL_128 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPMUL_256 x y;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_0);
    return ();
  }
  
  proc test_mulu (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 16)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPMULU_128 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPMULU_256 x y;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_0);
    return ();
  }
  
  proc test_shuffle (p:W64.t) : unit = {
    var aux: W128.t;
    
    var r:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSHUFB_128 r rotate24pattern;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_avx2 (p:W64.t) : unit = {
    var aux: W256.t;
    
    var r:W256.t;
    var s:W256.t;
    var t:W256.t;
    var u:W256.t;
    var v:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    r <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    s <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 64)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSHUFD_256 r (W8.of_int 51);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPBLEND_8u32 s t (W8.of_int 164);
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r `^` u);
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- v;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux);
    return ();
  }
  
  proc test_vpshuf (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var y:W256.t;
    var b:W128.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSHUFLW_128 a (W8.of_int 7);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSHUFHW_256 y (W8.of_int 42);
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (- 16))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (- 16)))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux_0);
    return ();
  }
  
  proc test_vpunpck (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 16)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPUNPCKH_16u8 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPUNPCKL_8u16 b c;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPUNPCKH_4u32 c a;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPUNPCKL_2u64 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    x <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 64)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPUNPCKL_32u8 x y;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPUNPCKH_16u16 y z;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPUNPCKL_8u32 z x;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPUNPCKH_4u64 x y;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux_0);
    return ();
  }
  
  proc test_vpandn (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 16)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPANDN_128 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    x <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 64)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPANDN_256 x y;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux_0);
    return ();
  }
  
  proc test_vpermq (p:W64.t) : unit = {
    var aux: W256.t;
    
    var x:W256.t;
    var y:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPERMQ x (W8.of_int 42);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPERM2I128 x y (W8.of_int 123);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_vpshift (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSLL_8u16 a (W8.of_int 1);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSLL_4u32 b (W8.of_int 2);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSLL_2u64 c (W8.of_int 3);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSLLV_4u32 c a;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSLLV_2u64 a b;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSLL_16u16 x (W8.of_int 1);
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSLL_8u32 y (W8.of_int 2);
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSLL_4u64 z (W8.of_int 3);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSLLV_8u32 z x;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPSLLV_4u64 x y;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- z;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux_0);
    return ();
  }
  
  proc test_vpextr (p:W64.t) : W64.t = {
    var aux_1: W8.t;
    var aux_3: W16.t;
    var aux: W32.t;
    var aux_2: W64.t;
    var aux_0: W128.t;
    
    var r64:W64.t;
    var r32:W32.t;
    var a:W128.t;
    var x:W32.t;
    var y:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    r32 <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- VPEXTR_8 a (W8.of_int 5);
    x <- zeroextu32(aux_1);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r32 + x);
    r32 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPEXTR_32 a (W8.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r32 + x);
    r32 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (zeroextu64 r32);
    r64 <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- VPEXTR_16 a (W8.of_int 3);
    y <- zeroextu64(aux_3);
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (r64 + y);
    r64 <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- VPEXTR_64 a (W8.of_int 1);
    y <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (r64 + y);
    r64 <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- VPEXTR_64 a (W8.of_int (- 128));
    y <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (r64 + y);
    r64 <- aux_2;
    return (r64);
  }
  
  proc test_extracti128 (p:W64.t) : unit = {
    var aux_0: W128.t;
    var aux: W256.t;
    
    var x:W256.t;
    var y:W128.t;
    var z:W128.t;
    var w:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VEXTRACTI128 x (W8.of_int 0);
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VEXTRACTI128 x (W8.of_int 1);
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (y `^` z);
    w <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- w;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux_0);
    return ();
  }
  
  proc test_vpinsr (p:W64.t) : unit = {
    var aux: W128.t;
    
    var a:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPINSR_2u64 a p (W8.of_int 0);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPINSR_4u32 a (truncateu32 p) (W8.of_int 1);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPINSR_8u16 a (truncateu16 p) (W8.of_int 2);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPINSR_16u8 a (truncateu8 p) (W8.of_int 3);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_vpbroadcast (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W256.t;
    var d:W256.t;
    var e:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPBROADCAST_16u8 (loadW8 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPBROADCAST_16u8 (truncateu8 a);
    b <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPBROADCAST_32u8 (loadW8 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPBROADCAST_32u8 (truncateu8 b);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- c;
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` d);
    e <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPBROADCAST_8u16 (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPBROADCAST_8u16 (truncateu16 a);
    b <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPBROADCAST_16u16 (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPBROADCAST_16u16 (truncateu16 b);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` c);
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` d);
    e <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPBROADCAST_4u32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPBROADCAST_4u32 (truncateu32 a);
    b <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPBROADCAST_8u32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPBROADCAST_8u32 (truncateu32 b);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` c);
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` d);
    e <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VPBROADCAST_2u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPBROADCAST_2u64 (truncateu64 a);
    b <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VPBROADCAST_4u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPBROADCAST_4u64 (truncateu64 b);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` c);
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` d);
    e <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int (16 * 0))))]) :: leakages;
    aux_0 <- VPBROADCAST_2u128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e `^` d);
    e <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- e;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (aux_0);
    return ();
  }
}.

