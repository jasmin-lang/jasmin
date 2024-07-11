require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.



abbrev rotate24pattern = W128.of_int 16028905388486802350658220295983399425.


module M = {
  proc test_mem128 (p:W64.t) : unit = {
    
    var r:W128.t;
    
    r <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (r);
    return ();
  }
  
  proc test_vmovdqa (p:W64.t) : unit = {
    
    var r:W128.t;
    
    r <- VMOVDQA_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (VMOVDQA_128 r);
    return ();
  }
  
  proc test_vmovdqu (p:W64.t) : unit = {
    
    var r:W128.t;
    
    r <- VMOVDQU_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (VMOVDQU_128 r);
    return ();
  }
  
  proc test_xor (p:W64.t) : unit = {
    
    var r:W128.t;
    var s:W128.t;
    var t:W128.t;
    var u:W128.t;
    
    r <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    s <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))));
    t <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 2)))));
    u <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 3)))));
    r <- (r `^` s);
    r <- (r `&` t);
    r <- (r `|` u);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (r);
    return ();
  }
  
  proc test_add (p:W64.t) : unit = {
    
    var r:W128.t;
    var s:W128.t;
    var u:W128.t;
    var t:W128.t;
    
    r <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    s <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))));
    u <- VPADD_16u8 r s;
    t <- VPADD_8u16 r u;
    r <- VPADD_4u32 s t;
    s <- VPADD_2u64 t r;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 1)))) (s);
    return ();
  }
  
  proc test_mul (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    c <- VPMUL_128 a b;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (c);
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    z <- VPMUL_256 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (z);
    return ();
  }
  
  proc test_mulu (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    c <- VPMULU_128 a b;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (c);
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    z <- VPMULU_256 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (z);
    return ();
  }
  
  proc test_shuffle (p:W64.t) : unit = {
    
    var r:W128.t;
    
    r <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    r <- VPSHUFB_128 r rotate24pattern;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (r);
    return ();
  }
  
  proc test_avx2 (p:W64.t) : unit = {
    
    var r:W256.t;
    var s:W256.t;
    var t:W256.t;
    var u:W256.t;
    var v:W256.t;
    
    r <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    s <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    t <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    r <- VPSHUFD_256 r (W8.of_int 51);
    u <- VPBLEND_8u32 s t (W8.of_int 164);
    v <- (r `^` u);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (v);
    return ();
  }
  
  proc test_vpshuf (p:W64.t) : unit = {
    
    var a:W128.t;
    var y:W256.t;
    var b:W128.t;
    var z:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    b <- VPSHUFLW_128 a (W8.of_int 7);
    z <- VPSHUFHW_256 y (W8.of_int 42);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int (- 16)))) (b);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (z);
    return ();
  }
  
  proc test_vpunpck (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    c <- VPUNPCKH_16u8 a b;
    a <- VPUNPCKL_8u16 b c;
    b <- VPUNPCKH_4u32 c a;
    c <- VPUNPCKL_2u64 a b;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (c);
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    y <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    z <- VPUNPCKL_32u8 x y;
    x <- VPUNPCKH_16u16 y z;
    y <- VPUNPCKL_8u32 z x;
    z <- VPUNPCKH_4u64 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (z);
    return ();
  }
  
  proc test_vpandn (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 16))));
    c <- VPANDN_128 a b;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (c);
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    y <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 64))));
    z <- VPANDN_256 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (z);
    return ();
  }
  
  proc test_vpermq (p:W64.t) : unit = {
    
    var x:W256.t;
    var y:W256.t;
    
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- VPERMQ x (W8.of_int 42);
    x <- VPERM2I128 x y (W8.of_int 123);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x);
    return ();
  }
  
  proc test_vpshift (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VPSLL_8u16 a (W8.of_int 1);
    c <- VPSLL_4u32 b (W8.of_int 2);
    a <- VPSLL_2u64 c (W8.of_int 3);
    b <- VPSLLV_4u32 c a;
    c <- VPSLLV_2u64 a b;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (c);
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))));
    y <- VPSLL_16u16 x (W8.of_int 1);
    z <- VPSLL_8u32 y (W8.of_int 2);
    x <- VPSLL_4u64 z (W8.of_int 3);
    y <- VPSLLV_8u32 z x;
    z <- VPSLLV_4u64 x y;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (z);
    return ();
  }
  
  proc test_vpextr (p:W64.t) : W64.t = {
    
    var r64:W64.t;
    var r32:W32.t;
    var a:W128.t;
    var x:W32.t;
    var y:W64.t;
    
    r32 <- (W32.of_int 0);
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- zeroextu32(VPEXTR_8 a (W8.of_int 5));
    r32 <- (r32 + x);
    x <- VPEXTR_32 a (W8.of_int 0);
    r32 <- (r32 + x);
    r64 <- (zeroextu64 r32);
    y <- zeroextu64(VPEXTR_16 a (W8.of_int 3));
    r64 <- (r64 + y);
    y <- VPEXTR_64 a (W8.of_int 1);
    r64 <- (r64 + y);
    y <- VPEXTR_64 a (W8.of_int (- 128));
    r64 <- (r64 + y);
    return (r64);
  }
  
  proc test_extracti128 (p:W64.t) : unit = {
    
    var x:W256.t;
    var y:W128.t;
    var z:W128.t;
    var w:W128.t;
    
    x <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- VEXTRACTI128 x (W8.of_int 0);
    z <- VEXTRACTI128 x (W8.of_int 1);
    w <- (y `^` z);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (w);
    return ();
  }
  
  proc test_vpinsr (p:W64.t) : unit = {
    
    var a:W128.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- VPINSR_2u64 a p (W8.of_int 0);
    a <- VPINSR_4u32 a (truncateu32 p) (W8.of_int 1);
    a <- VPINSR_8u16 a (truncateu16 p) (W8.of_int 2);
    a <- VPINSR_16u8 a (truncateu8 p) (W8.of_int 3);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (a);
    return ();
  }
  
  proc test_vpbroadcast (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W256.t;
    var d:W256.t;
    var e:W256.t;
    
    a <- VPBROADCAST_16u8 (loadW8 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VPBROADCAST_16u8 (truncateu8 a);
    c <- VPBROADCAST_32u8 (loadW8 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    d <- VPBROADCAST_32u8 (truncateu8 b);
    e <- c;
    e <- (e `^` d);
    a <- VPBROADCAST_8u16 (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VPBROADCAST_8u16 (truncateu16 a);
    c <- VPBROADCAST_16u16 (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    d <- VPBROADCAST_16u16 (truncateu16 b);
    e <- (e `^` c);
    e <- (e `^` d);
    a <- VPBROADCAST_4u32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VPBROADCAST_4u32 (truncateu32 a);
    c <- VPBROADCAST_8u32 (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    d <- VPBROADCAST_8u32 (truncateu32 b);
    e <- (e `^` c);
    e <- (e `^` d);
    a <- VPBROADCAST_2u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VPBROADCAST_2u64 (truncateu64 a);
    c <- VPBROADCAST_4u64 (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    d <- VPBROADCAST_4u64 (truncateu64 b);
    e <- (e `^` c);
    e <- (e `^` d);
    d <- VPBROADCAST_2u128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int (16 * 0)))));
    e <- (e `^` d);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 32))) (e);
    return ();
  }
}.

