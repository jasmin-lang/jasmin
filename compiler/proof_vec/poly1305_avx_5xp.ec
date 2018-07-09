require import List Jasmin_model Int IntDiv CoreMap.


abbrev zero_u128 = W128.of_uint 0.


abbrev five_u128 = W128.of_uint 92233720368547758085.


abbrev bit25_u128 = W128.of_uint 309485009821345068741558272.


abbrev mask26_u128 = W128.of_uint 1237940020838636201256681471.


module M = {
  proc add (x:W64.t Array5.t, y:W64.t Array5.t) : W64.t Array5.t = {
    
    var i:int;
    
    i <- 0;
    while (i < 5) {
      x.[i] <- (x.[i] + y.[i]);
      i <- i + 1;
    }
    return (x);
  }
  
  proc add_carry (x:W64.t Array5.t, y:W64.t Array5.t) : W64.t Array5.t = {
    
    var i:int;
    var c:W64.t;
    
    x.[0] <- (x.[0] + y.[0]);
    i <- 0;
    while (i < 4) {
      c <- x.[i];
      c <- (c `>>` (W8.of_uint 26));
      x.[i] <- (x.[i] `&` (W64.of_uint 67108863));
      x.[(i + 1)] <- (x.[(i + 1)] + y.[(i + 1)]);
      x.[(i + 1)] <- (x.[(i + 1)] + c);
      i <- i + 1;
    }
    return (x);
  }
  
  proc add_u128 (x:W128.t Array5.t, y:W128.t Array5.t) : W128.t Array5.t = {
    
    var i:int;
    
    i <- 0;
    while (i < 5) {
      x.[i] <- x86_VPADD_2u64 x.[i] y.[i];
      i <- i + 1;
    }
    return (x);
  }
  
  proc hadd_u128 (x:W128.t Array5.t) : W64.t Array5.t = {
    
    var h:W64.t Array5.t;
    var i:int;
    var t:W64.t Array5.t;
    h <- Array5.init W64.zeros;
    t <- Array5.init W64.zeros;
    i <- 0;
    while (i < 5) {
      t.[i] <- x86_VPEXTR_64 x.[i] (W8.of_uint 1);
      h.[i] <- x86_VPEXTR_64 x.[i] (W8.of_uint 0);
      i <- i + 1;
    }
    h <@ add_carry (h, t);
    return (h);
  }
  
  proc freeze (x:W64.t Array5.t) : W64.t Array5.t = {
    
    var ox:W64.t Array5.t;
    var mp:W64.t Array5.t;
    var n:W64.t;
    mp <- Array5.init W64.zeros;
    ox <- Array5.init W64.zeros;
    ox <- x;
    mp.[0] <- (W64.of_uint 5);
    mp.[1] <- (W64.of_uint 0);
    mp.[2] <- (W64.of_uint 0);
    mp.[3] <- (W64.of_uint 0);
    mp.[4] <- (W64.of_uint 67108864);
    x <@ add_carry (x, mp);
    n <- x.[4];
    n <- (n `>>` (W8.of_uint 26));
    n <- (n `&` (W64.of_uint 1));
    n <- (- n);
    ox.[0] <- (ox.[0] `^` x.[0]);
    ox.[1] <- (ox.[1] `^` x.[1]);
    ox.[2] <- (ox.[2] `^` x.[2]);
    ox.[3] <- (ox.[3] `^` x.[3]);
    ox.[4] <- (ox.[4] `^` x.[4]);
    ox.[0] <- (ox.[0] `&` n);
    ox.[1] <- (ox.[1] `&` n);
    ox.[2] <- (ox.[2] `&` n);
    ox.[3] <- (ox.[3] `&` n);
    ox.[4] <- (ox.[4] `&` n);
    x.[0] <- (x.[0] `^` ox.[0]);
    x.[1] <- (x.[1] `^` ox.[1]);
    x.[2] <- (x.[2] `^` ox.[2]);
    x.[3] <- (x.[3] `^` ox.[3]);
    x.[4] <- (x.[4] `^` ox.[4]);
    return (x);
  }
  
  proc unpack (m:W64.t) : W64.t Array5.t = {
    
    var x:W64.t Array5.t;
    var m0:W64.t;
    var m1:W64.t;
    var t:W64.t;
    x <- Array5.init W64.zeros;
    m0 <- (loadW64 Glob.mem (m + (W64.of_uint (8 * 0))));
    m1 <- (loadW64 Glob.mem (m + (W64.of_uint (8 * 1))));
    x.[0] <- m0;
    x.[0] <- (x.[0] `&` (W64.of_uint 67108863));
    m0 <- (m0 `>>` (W8.of_uint 26));
    x.[1] <- m0;
    x.[1] <- (x.[1] `&` (W64.of_uint 67108863));
    m0 <- (m0 `>>` (W8.of_uint 26));
    x.[2] <- m0;
    t <- m1;
    t <- (t `<<` (W8.of_uint 12));
    x.[2] <- (x.[2] `|` t);
    x.[2] <- (x.[2] `&` (W64.of_uint 67108863));
    m1 <- (m1 `>>` (W8.of_uint 14));
    x.[3] <- m1;
    x.[3] <- (x.[3] `&` (W64.of_uint 67108863));
    m1 <- (m1 `>>` (W8.of_uint 26));
    x.[4] <- m1;
    return (x);
  }
  
  proc mulmod_12 (x:W64.t Array5.t, y:W64.t Array5.t, yx5:W64.t Array4.t) : 
  W64.t Array5.t = {
    
    var t:W64.t Array5.t;
    var z:W64.t Array3.t;
    t <- Array5.init W64.zeros;
    z <- Array3.init W64.zeros;
    t.[0] <- x.[0];
    t.[0] <- (t.[0] * y.[0]);
    t.[1] <- x.[0];
    t.[1] <- (t.[1] * y.[1]);
    t.[2] <- x.[0];
    t.[2] <- (t.[2] * y.[2]);
    t.[3] <- x.[0];
    t.[3] <- (t.[3] * y.[3]);
    t.[4] <- x.[0];
    t.[4] <- (t.[4] * y.[4]);
    z.[0] <- x.[1];
    z.[0] <- (z.[0] * y.[0]);
    z.[1] <- x.[1];
    z.[1] <- (z.[1] * y.[1]);
    z.[2] <- x.[1];
    z.[2] <- (z.[2] * y.[2]);
    t.[1] <- (t.[1] + z.[0]);
    t.[2] <- (t.[2] + z.[1]);
    t.[3] <- (t.[3] + z.[2]);
    z.[0] <- x.[1];
    z.[0] <- (z.[0] * y.[3]);
    z.[1] <- x.[2];
    z.[1] <- (z.[1] * y.[0]);
    z.[2] <- x.[2];
    z.[2] <- (z.[2] * y.[1]);
    t.[4] <- (t.[4] + z.[0]);
    t.[2] <- (t.[2] + z.[1]);
    t.[3] <- (t.[3] + z.[2]);
    z.[0] <- x.[2];
    z.[0] <- (z.[0] * y.[2]);
    z.[1] <- x.[3];
    z.[1] <- (z.[1] * y.[0]);
    z.[2] <- x.[3];
    z.[2] <- (z.[2] * y.[1]);
    t.[4] <- (t.[4] + z.[0]);
    z.[0] <- x.[4];
    z.[0] <- (z.[0] * y.[0]);
    t.[3] <- (t.[3] + z.[1]);
    t.[4] <- (t.[4] + z.[2]);
    t.[4] <- (t.[4] + z.[0]);
    z.[0] <- x.[4];
    z.[0] <- (z.[0] * yx5.[0]);
    z.[1] <- x.[3];
    z.[1] <- (z.[1] * yx5.[1]);
    z.[2] <- x.[4];
    z.[2] <- (z.[2] * yx5.[1]);
    t.[0] <- (t.[0] + z.[0]);
    t.[0] <- (t.[0] + z.[1]);
    t.[1] <- (t.[1] + z.[2]);
    z.[0] <- x.[4];
    z.[0] <- (z.[0] * yx5.[2]);
    z.[1] <- x.[2];
    z.[1] <- (z.[1] * yx5.[2]);
    z.[2] <- x.[3];
    z.[2] <- (z.[2] * yx5.[2]);
    t.[2] <- (t.[2] + z.[0]);
    t.[0] <- (t.[0] + z.[1]);
    t.[1] <- (t.[1] + z.[2]);
    z.[0] <- x.[1];
    z.[0] <- (z.[0] * yx5.[3]);
    z.[1] <- x.[2];
    z.[1] <- (z.[1] * yx5.[3]);
    z.[2] <- x.[3];
    z.[2] <- (z.[2] * yx5.[3]);
    x.[0] <- t.[0];
    x.[0] <- (x.[0] + z.[0]);
    z.[0] <- x.[4];
    z.[0] <- (z.[0] * yx5.[3]);
    x.[1] <- t.[1];
    x.[1] <- (x.[1] + z.[1]);
    x.[2] <- t.[2];
    x.[2] <- (x.[2] + z.[2]);
    x.[3] <- t.[3];
    x.[3] <- (x.[3] + z.[0]);
    x.[4] <- t.[4];
    return (x);
  }
  
  proc carry_reduce (x:W64.t Array5.t) : W64.t Array5.t = {
    
    var z:W64.t Array2.t;
    z <- Array2.init W64.zeros;
    z.[0] <- x.[0];
    z.[0] <- (z.[0] `>>` (W8.of_uint 26));
    z.[1] <- x.[3];
    z.[1] <- (z.[1] `>>` (W8.of_uint 26));
    x.[0] <- (x.[0] `&` (W64.of_uint 67108863));
    x.[3] <- (x.[3] `&` (W64.of_uint 67108863));
    x.[1] <- (x.[1] + z.[0]);
    x.[4] <- (x.[4] + z.[1]);
    z.[0] <- x.[1];
    z.[0] <- (z.[0] `>>` (W8.of_uint 26));
    z.[1] <- x.[4];
    z.[1] <- (z.[1] `>>` (W8.of_uint 26));
    z.[1] <- (z.[1] `&` (W64.of_uint 4294967295));
    z.[1] <- (z.[1] * (W64.of_uint 5));
    x.[1] <- (x.[1] `&` (W64.of_uint 67108863));
    x.[4] <- (x.[4] `&` (W64.of_uint 67108863));
    x.[2] <- (x.[2] + z.[0]);
    x.[0] <- (x.[0] + z.[1]);
    z.[0] <- x.[2];
    z.[0] <- (z.[0] `>>` (W8.of_uint 26));
    z.[1] <- x.[0];
    z.[1] <- (z.[1] `>>` (W8.of_uint 26));
    x.[2] <- (x.[2] `&` (W64.of_uint 67108863));
    x.[0] <- (x.[0] `&` (W64.of_uint 67108863));
    x.[3] <- (x.[3] + z.[0]);
    x.[1] <- (x.[1] + z.[1]);
    z.[0] <- x.[3];
    z.[0] <- (z.[0] `>>` (W8.of_uint 26));
    x.[3] <- (x.[3] `&` (W64.of_uint 67108863));
    x.[4] <- (x.[4] + z.[0]);
    return (x);
  }
  
  proc unpack_u26x5x2_to_u26x5x2 (s:W64.t Array5.t, t:W64.t Array5.t) : 
  W128.t Array5.t = {
    
    var r:W128.t Array5.t;
    var i:int;
    r <- Array5.init W128.zeros;
    i <- 0;
    while (i < 5) {
      r.[i] <- zero_u128;
      r.[i] <- x86_VPINSR_2u64 r.[i] s.[i] (W8.of_uint 0);
      r.[i] <- x86_VPINSR_2u64 r.[i] t.[i] (W8.of_uint 1);
      i <- i + 1;
    }
    return (r);
  }
  
  proc unpack_u128x2_to_u26x5x2 (m:W64.t) : W128.t Array5.t = {
    
    var r:W128.t Array5.t;
    var s128:W128.t;
    var t128:W128.t;
    var t1:W128.t;
    var t2:W128.t;
    var t3:W128.t;
    r <- Array5.init W128.zeros;
    s128 <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 0))));
    t128 <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 2))));
    t1 <- x86_VPUNPCKL_2u64 s128 t128;
    s128 <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 1))));
    t128 <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 3))));
    t2 <- x86_VPUNPCKL_2u64 s128 t128;
    t3 <- x86_VPSLL_2u64 t2 (W8.of_uint 12);
    r.[0] <- x86_VPAND_128 t1 mask26_u128;
    t1 <- x86_VPSRL_2u64 t1 (W8.of_uint 26);
    r.[1] <- x86_VPAND_128 t1 mask26_u128;
    t1 <- x86_VPSRL_2u64 t1 (W8.of_uint 26);
    t1 <- x86_VPOR_128 t1 t3;
    r.[2] <- x86_VPAND_128 t1 mask26_u128;
    t1 <- x86_VPSRL_2u64 t1 (W8.of_uint 26);
    r.[3] <- x86_VPAND_128 t1 mask26_u128;
    r.[4] <- x86_VPSRL_2u64 t2 (W8.of_uint 40);
    r.[4] <- x86_VPOR_128 r.[4] bit25_u128;
    return (r);
  }
  
  proc mulmod_u128 (x:W128.t Array5.t, y:W128.t Array5.t, yx5:W128.t Array4.t) : 
  W128.t Array5.t = {
    
    var t:W128.t Array5.t;
    var z:W128.t Array5.t;
    t <- Array5.init W128.zeros;
    z <- Array5.init W128.zeros;
    t.[0] <- x86_VPMULU_128 x.[0] y.[0];
    t.[1] <- x86_VPMULU_128 x.[0] y.[1];
    t.[2] <- x86_VPMULU_128 x.[0] y.[2];
    t.[3] <- x86_VPMULU_128 x.[0] y.[3];
    t.[4] <- x86_VPMULU_128 x.[0] y.[4];
    z.[0] <- x86_VPMULU_128 x.[1] y.[0];
    z.[1] <- x86_VPMULU_128 x.[1] y.[1];
    z.[2] <- x86_VPMULU_128 x.[1] y.[2];
    z.[3] <- x86_VPMULU_128 x.[1] y.[3];
    z.[4] <- x86_VPMULU_128 x.[2] y.[0];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[0];
    t.[2] <- x86_VPADD_2u64 t.[2] z.[1];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[2];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[3];
    t.[2] <- x86_VPADD_2u64 t.[2] z.[4];
    z.[0] <- x86_VPMULU_128 x.[2] y.[1];
    z.[1] <- x86_VPMULU_128 x.[2] y.[2];
    z.[2] <- x86_VPMULU_128 x.[3] y.[0];
    z.[3] <- x86_VPMULU_128 x.[3] y.[1];
    z.[4] <- x86_VPMULU_128 x.[4] y.[0];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[0];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[1];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[2];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[3];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[4];
    z.[0] <- x86_VPMULU_128 x.[4] yx5.[0];
    z.[1] <- x86_VPMULU_128 x.[3] yx5.[1];
    z.[2] <- x86_VPMULU_128 x.[4] yx5.[1];
    z.[3] <- x86_VPMULU_128 x.[2] yx5.[2];
    z.[4] <- x86_VPMULU_128 x.[3] yx5.[2];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[0];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[2];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[1];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[4];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[3];
    z.[0] <- x86_VPMULU_128 x.[4] yx5.[2];
    z.[1] <- x86_VPMULU_128 x.[1] yx5.[3];
    z.[2] <- x86_VPMULU_128 x.[2] yx5.[3];
    z.[3] <- x86_VPMULU_128 x.[3] yx5.[3];
    z.[4] <- x86_VPMULU_128 x.[4] yx5.[3];
    t.[2] <- x86_VPADD_2u64 t.[2] z.[0];
    x.[0] <- x86_VPADD_2u64 t.[0] z.[1];
    x.[1] <- x86_VPADD_2u64 t.[1] z.[2];
    x.[2] <- x86_VPADD_2u64 t.[2] z.[3];
    x.[3] <- x86_VPADD_2u64 t.[3] z.[4];
    x.[4] <- t.[4];
    return (x);
  }
  
  proc mulmod_u128_prefetch (in_0:W64.t, x:W128.t Array5.t,
                             y:W128.t Array5.t, yx5:W128.t Array4.t) : 
  W128.t Array5.t * W128.t Array5.t = {
    
    var xy0:W128.t Array5.t;
    var t:W128.t Array5.t;
    var z:W128.t Array5.t;
    t <- Array5.init W128.zeros;
    xy0 <- Array5.init W128.zeros;
    z <- Array5.init W128.zeros;
    t.[0] <- x86_VPMULU_128 x.[0] y.[0];
    t.[1] <- x86_VPMULU_128 x.[0] y.[1];
    t.[2] <- x86_VPMULU_128 x.[0] y.[2];
    t.[3] <- x86_VPMULU_128 x.[0] y.[3];
    t.[4] <- x86_VPMULU_128 x.[0] y.[4];
    z.[0] <- x86_VPMULU_128 x.[1] y.[0];
    z.[1] <- x86_VPMULU_128 x.[1] y.[1];
    z.[2] <- x86_VPMULU_128 x.[1] y.[2];
    z.[3] <- x86_VPMULU_128 x.[1] y.[3];
    z.[4] <- x86_VPMULU_128 x.[2] y.[0];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[0];
    t.[2] <- x86_VPADD_2u64 t.[2] z.[1];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[2];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[3];
    t.[2] <- x86_VPADD_2u64 t.[2] z.[4];
    z.[0] <- x86_VPMULU_128 x.[2] y.[1];
    z.[1] <- x86_VPMULU_128 x.[2] y.[2];
    z.[2] <- x86_VPMULU_128 x.[3] y.[0];
    z.[3] <- x86_VPMULU_128 x.[3] y.[1];
    z.[4] <- x86_VPMULU_128 x.[4] y.[0];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[0];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[1];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[2];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[3];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[4];
    z.[0] <- x86_VPMULU_128 x.[4] yx5.[0];
    z.[1] <- x86_VPMULU_128 x.[3] yx5.[1];
    z.[2] <- x86_VPMULU_128 x.[4] yx5.[1];
    z.[3] <- x86_VPMULU_128 x.[2] yx5.[2];
    z.[4] <- x86_VPMULU_128 x.[3] yx5.[2];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[0];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[2];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[1];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[4];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[3];
    z.[0] <- x86_VPMULU_128 x.[4] yx5.[2];
    z.[1] <- x86_VPMULU_128 x.[1] yx5.[3];
    z.[2] <- x86_VPMULU_128 x.[2] yx5.[3];
    z.[3] <- x86_VPMULU_128 x.[3] yx5.[3];
    z.[4] <- x86_VPMULU_128 x.[4] yx5.[3];
    xy0 <@ unpack_u128x2_to_u26x5x2 (in_0);
    t.[2] <- x86_VPADD_2u64 t.[2] z.[0];
    x.[0] <- x86_VPADD_2u64 t.[0] z.[1];
    x.[1] <- x86_VPADD_2u64 t.[1] z.[2];
    x.[2] <- x86_VPADD_2u64 t.[2] z.[3];
    x.[3] <- x86_VPADD_2u64 t.[3] z.[4];
    x.[4] <- t.[4];
    return (x, xy0);
  }
  
  proc mulmod_add_u128_prefetch (in_0:W64.t, u:W128.t Array5.t,
                                 x:W128.t Array5.t, y:W128.t Array5.t,
                                 yx5:W128.t Array4.t) : W128.t Array5.t *
                                                        W128.t Array5.t = {
    
    var xy1:W128.t Array5.t;
    var t:W128.t Array5.t;
    var z:W128.t Array5.t;
    t <- Array5.init W128.zeros;
    xy1 <- Array5.init W128.zeros;
    z <- Array5.init W128.zeros;
    t.[0] <- x86_VPMULU_128 x.[0] y.[0];
    t.[1] <- x86_VPMULU_128 x.[0] y.[1];
    t.[2] <- x86_VPMULU_128 x.[0] y.[2];
    t.[3] <- x86_VPMULU_128 x.[0] y.[3];
    t.[4] <- x86_VPMULU_128 x.[0] y.[4];
    t <@ add_u128 (t, u);
    z.[0] <- x86_VPMULU_128 x.[1] y.[0];
    z.[1] <- x86_VPMULU_128 x.[1] y.[1];
    z.[2] <- x86_VPMULU_128 x.[1] y.[2];
    z.[3] <- x86_VPMULU_128 x.[1] y.[3];
    z.[4] <- x86_VPMULU_128 x.[2] y.[0];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[0];
    t.[2] <- x86_VPADD_2u64 t.[2] z.[1];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[2];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[3];
    t.[2] <- x86_VPADD_2u64 t.[2] z.[4];
    z.[0] <- x86_VPMULU_128 x.[2] y.[1];
    z.[1] <- x86_VPMULU_128 x.[2] y.[2];
    z.[2] <- x86_VPMULU_128 x.[3] y.[0];
    z.[3] <- x86_VPMULU_128 x.[3] y.[1];
    z.[4] <- x86_VPMULU_128 x.[4] y.[0];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[0];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[1];
    t.[3] <- x86_VPADD_2u64 t.[3] z.[2];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[3];
    t.[4] <- x86_VPADD_2u64 t.[4] z.[4];
    z.[0] <- x86_VPMULU_128 x.[4] yx5.[0];
    z.[1] <- x86_VPMULU_128 x.[3] yx5.[1];
    z.[2] <- x86_VPMULU_128 x.[4] yx5.[1];
    z.[3] <- x86_VPMULU_128 x.[2] yx5.[2];
    z.[4] <- x86_VPMULU_128 x.[3] yx5.[2];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[0];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[2];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[1];
    t.[1] <- x86_VPADD_2u64 t.[1] z.[4];
    t.[0] <- x86_VPADD_2u64 t.[0] z.[3];
    z.[0] <- x86_VPMULU_128 x.[4] yx5.[2];
    z.[1] <- x86_VPMULU_128 x.[1] yx5.[3];
    z.[2] <- x86_VPMULU_128 x.[2] yx5.[3];
    z.[3] <- x86_VPMULU_128 x.[3] yx5.[3];
    z.[4] <- x86_VPMULU_128 x.[4] yx5.[3];
    xy1 <@ unpack_u128x2_to_u26x5x2 (in_0);
    t.[2] <- x86_VPADD_2u64 t.[2] z.[0];
    u.[0] <- x86_VPADD_2u64 t.[0] z.[1];
    u.[1] <- x86_VPADD_2u64 t.[1] z.[2];
    u.[2] <- x86_VPADD_2u64 t.[2] z.[3];
    u.[3] <- x86_VPADD_2u64 t.[3] z.[4];
    u.[4] <- t.[4];
    return (u, xy1);
  }
  
  proc carry_reduce_u128 (x:W128.t Array5.t) : W128.t Array5.t = {
    
    var z:W128.t Array2.t;
    z <- Array2.init W128.zeros;
    z.[0] <- x86_VPSRL_2u64 x.[0] (W8.of_uint 26);
    z.[1] <- x86_VPSRL_2u64 x.[3] (W8.of_uint 26);
    x.[0] <- x86_VPAND_128 x.[0] mask26_u128;
    x.[3] <- x86_VPAND_128 x.[3] mask26_u128;
    x.[1] <- x86_VPADD_2u64 x.[1] z.[0];
    x.[4] <- x86_VPADD_2u64 x.[4] z.[1];
    z.[0] <- x86_VPSRL_2u64 x.[1] (W8.of_uint 26);
    z.[1] <- x86_VPSRL_2u64 x.[4] (W8.of_uint 26);
    z.[1] <- x86_VPMULU_128 z.[1] five_u128;
    x.[1] <- x86_VPAND_128 x.[1] mask26_u128;
    x.[4] <- x86_VPAND_128 x.[4] mask26_u128;
    x.[2] <- x86_VPADD_2u64 x.[2] z.[0];
    x.[0] <- x86_VPADD_2u64 x.[0] z.[1];
    z.[0] <- x86_VPSRL_2u64 x.[2] (W8.of_uint 26);
    z.[1] <- x86_VPSRL_2u64 x.[0] (W8.of_uint 26);
    x.[2] <- x86_VPAND_128 x.[2] mask26_u128;
    x.[0] <- x86_VPAND_128 x.[0] mask26_u128;
    x.[3] <- x86_VPADD_2u64 x.[3] z.[0];
    x.[1] <- x86_VPADD_2u64 x.[1] z.[1];
    z.[0] <- x86_VPSRL_2u64 x.[3] (W8.of_uint 26);
    x.[3] <- x86_VPAND_128 x.[3] mask26_u128;
    x.[4] <- x86_VPADD_2u64 x.[4] z.[0];
    return (x);
  }
  
  proc clamp (k:W64.t) : W64.t Array5.t = {
    
    var r:W64.t Array5.t;
    r <- Array5.init W64.zeros;
    r <@ unpack (k);
    r.[0] <- (r.[0] `&` (W64.of_uint 67108863));
    r.[1] <- (r.[1] `&` (W64.of_uint 67108611));
    r.[2] <- (r.[2] `&` (W64.of_uint 67092735));
    r.[3] <- (r.[3] `&` (W64.of_uint 66076671));
    r.[4] <- (r.[4] `&` (W64.of_uint 1048575));
    return (r);
  }
  
  proc load (in_0:W64.t) : W64.t Array5.t = {
    
    var x:W64.t Array5.t;
    x <- Array5.init W64.zeros;
    x <@ unpack (in_0);
    x.[4] <- (x.[4] `|` (W64.of_uint 16777216));
    return (x);
  }
  
  proc load_last (in_0:W64.t, inlen:W64.t) : W64.t Array5.t = {
    
    var x:W64.t Array5.t;
    var i:int;
    var m:W64.t Array2.t;
    var c:W64.t;
    var n:W64.t;
    var t:W64.t;
    m <- Array2.init W64.zeros;
    x <- Array5.init W64.zeros;
    i <- 0;
    while (i < 2) {
      m.[i] <- (W64.of_uint 0);
      i <- i + 1;
    }
    if ((inlen \ult (W64.of_uint 8))) {
      c <- (W64.of_uint 0);
      n <- (W64.of_uint 0);
      
      while ((c \ult inlen)) {
        t <- (zeroext_8_64 (loadW8 Glob.mem (in_0 + c)));
        t <- (t `<<` (zeroext_64_8 n));
        m.[0] <- (m.[0] `|` t);
        n <- (n + (W64.of_uint 8));
        c <- (c + (W64.of_uint 1));
      }
      t <- (W64.of_uint 1);
      t <- (t `<<` (zeroext_64_8 n));
      m.[0] <- (m.[0] `|` t);
    } else {
      m.[0] <- (loadW64 Glob.mem (in_0 + (W64.of_uint 0)));
      inlen <- (inlen - (W64.of_uint 8));
      in_0 <- (in_0 + (W64.of_uint 8));
      c <- (W64.of_uint 0);
      n <- (W64.of_uint 0);
      
      while ((c \ult inlen)) {
        t <- (zeroext_8_64 (loadW8 Glob.mem (in_0 + c)));
        t <- (t `<<` (zeroext_64_8 n));
        m.[1] <- (m.[1] `|` t);
        n <- (n + (W64.of_uint 8));
        c <- (c + (W64.of_uint 1));
      }
      t <- (W64.of_uint 1);
      t <- (t `<<` (zeroext_64_8 n));
      m.[1] <- (m.[1] `|` t);
    }
    x.[0] <- m.[0];
    x.[0] <- (x.[0] `&` (W64.of_uint 67108863));
    m.[0] <- (m.[0] `>>` (W8.of_uint 26));
    x.[1] <- m.[0];
    x.[1] <- (x.[1] `&` (W64.of_uint 67108863));
    m.[0] <- (m.[0] `>>` (W8.of_uint 26));
    x.[2] <- m.[0];
    t <- m.[1];
    t <- (t `<<` (W8.of_uint 12));
    x.[2] <- (x.[2] `|` t);
    x.[2] <- (x.[2] `&` (W64.of_uint 67108863));
    m.[1] <- (m.[1] `>>` (W8.of_uint 14));
    x.[3] <- m.[1];
    x.[3] <- (x.[3] `&` (W64.of_uint 67108863));
    m.[1] <- (m.[1] `>>` (W8.of_uint 26));
    x.[4] <- m.[1];
    return (x);
  }
  
  proc pack (y:W64.t, x:W64.t Array5.t) : unit = {
    
    var t:W64.t;
    var t1:W64.t;
    
    t <- x.[0];
    t1 <- x.[1];
    t1 <- (t1 `<<` (W8.of_uint 26));
    t <- (t `|` t1);
    t1 <- x.[2];
    t1 <- (t1 `<<` (W8.of_uint 52));
    t <- (t `|` t1);
    Glob.mem <- storeW64 Glob.mem (y + (W64.of_uint (0 * 8))) t;
    t <- x.[2];
    t <- (t `&` (W64.of_uint 67108863));
    t <- (t `>>` (W8.of_uint 12));
    t1 <- x.[3];
    t1 <- (t1 `<<` (W8.of_uint 14));
    t <- (t `|` t1);
    t1 <- x.[4];
    t1 <- (t1 `<<` (W8.of_uint 40));
    t <- (t `|` t1);
    Glob.mem <- storeW64 Glob.mem (y + (W64.of_uint (1 * 8))) t;
    return ();
  }
  
  proc first_block (in_0:W64.t, s_r2r2:W128.t Array5.t,
                    s_r2r2x5:W128.t Array4.t) : W128.t Array5.t * W64.t = {
    
    var hxy:W128.t Array5.t;
    var xy0:W128.t Array5.t;
    var xy1:W128.t Array5.t;
    hxy <- Array5.init W128.zeros;
    xy0 <- Array5.init W128.zeros;
    xy1 <- Array5.init W128.zeros;
    xy0 <@ unpack_u128x2_to_u26x5x2 (in_0);
    in_0 <- (in_0 + (W64.of_uint 32));
    hxy <@ mulmod_u128 (xy0, s_r2r2, s_r2r2x5);
    xy1 <@ unpack_u128x2_to_u26x5x2 (in_0);
    in_0 <- (in_0 + (W64.of_uint 32));
    hxy <@ add_u128 (hxy, xy1);
    hxy <@ carry_reduce_u128 (hxy);
    return (hxy, in_0);
  }
  
  proc remaining_blocks (hxy:W128.t Array5.t, in_0:W64.t,
                         s_r4r4:W128.t Array5.t, s_r4r4x5:W128.t Array4.t,
                         s_r2r2:W128.t Array5.t, s_r2r2x5:W128.t Array4.t) : 
  W128.t Array5.t * W64.t = {
    
    var xy0:W128.t Array5.t;
    var xy1:W128.t Array5.t;
    xy0 <- Array5.init W128.zeros;
    xy1 <- Array5.init W128.zeros;
    (hxy, xy0) <@ mulmod_u128_prefetch (in_0, hxy, s_r4r4, s_r4r4x5);
    in_0 <- (in_0 + (W64.of_uint 32));
    (hxy, xy1) <@ mulmod_add_u128_prefetch (in_0, hxy, xy0, s_r2r2,
    s_r2r2x5);
    in_0 <- (in_0 + (W64.of_uint 32));
    hxy <@ add_u128 (hxy, xy1);
    hxy <@ carry_reduce_u128 (hxy);
    return (hxy, in_0);
  }
  
  proc final_mul (hxy:W128.t Array5.t, s_r2r:W128.t Array5.t,
                  s_r2rx5:W128.t Array4.t) : W64.t Array5.t = {
    
    var h:W64.t Array5.t;
    h <- Array5.init W64.zeros;
    hxy <@ mulmod_u128 (hxy, s_r2r, s_r2rx5);
    hxy <@ carry_reduce_u128 (hxy);
    h <@ hadd_u128 (hxy);
    return (h);
  }
  
  proc poly1305 (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    
    var s_out:W64.t;
    var s_in:W64.t;
    var s_inlen:W64.t;
    var s_k:W64.t;
    var r:W64.t Array5.t;
    var s_r:W64.t Array5.t;
    var i:int;
    var t:W64.t;
    var s_rx5:W64.t Array4.t;
    var h:W64.t Array5.t;
    var b64:W64.t;
    var s_b64:W64.t;
    var r2:W64.t Array5.t;
    var s_r2:W64.t Array5.t;
    var s_r2x5:W64.t Array4.t;
    var r2r:W128.t Array5.t;
    var s_r2r:W128.t Array5.t;
    var t_u128:W128.t;
    var s_r2rx5:W128.t Array4.t;
    var r2r2:W128.t Array5.t;
    var s_r2r2:W128.t Array5.t;
    var s_r2r2x5:W128.t Array4.t;
    var r4:W64.t Array5.t;
    var r4r4:W128.t Array5.t;
    var s_r4r4:W128.t Array5.t;
    var s_r4r4x5:W128.t Array4.t;
    var hxy:W128.t Array5.t;
    var b16:W64.t;
    var x:W64.t Array5.t;
    var s:W64.t Array5.t;
    h <- Array5.init W64.zeros;
    hxy <- Array5.init W128.zeros;
    r <- Array5.init W64.zeros;
    r2 <- Array5.init W64.zeros;
    r2r <- Array5.init W128.zeros;
    r2r2 <- Array5.init W128.zeros;
    r4 <- Array5.init W64.zeros;
    r4r4 <- Array5.init W128.zeros;
    s <- Array5.init W64.zeros;
    s_r <- Array5.init W64.zeros;
    s_r2 <- Array5.init W64.zeros;
    s_r2r <- Array5.init W128.zeros;
    s_r2r2 <- Array5.init W128.zeros;
    s_r2r2x5 <- Array4.init W128.zeros;
    s_r2rx5 <- Array4.init W128.zeros;
    s_r2x5 <- Array4.init W64.zeros;
    s_r4r4 <- Array5.init W128.zeros;
    s_r4r4x5 <- Array4.init W128.zeros;
    s_rx5 <- Array4.init W64.zeros;
    x <- Array5.init W64.zeros;
    s_out <- out;
    s_in <- in_0;
    s_inlen <- inlen;
    s_k <- k;
    r <@ clamp (k);
    s_r <- r;
    i <- 0;
    while (i < 4) {
      t <- (r.[(i + 1)] * (W64.of_uint 5));
      s_rx5.[i] <- t;
      i <- i + 1;
    }
    i <- 0;
    while (i < 5) {
      h.[i] <- (W64.of_uint 0);
      i <- i + 1;
    }
    b64 <- inlen;
    b64 <- (b64 `>>` (W8.of_uint 6));
    if (((W64.of_uint 0) \ult b64)) {
      s_b64 <- b64;
      r2 <- r;
      r2 <@ mulmod_12 (r2, s_r, s_rx5);
      r2 <@ carry_reduce (r2);
      s_r2 <- r2;
      i <- 0;
      while (i < 4) {
        t <- (r2.[(i + 1)] * (W64.of_uint 5));
        s_r2x5.[i] <- t;
        i <- i + 1;
      }
      r <- s_r;
      r2r <@ unpack_u26x5x2_to_u26x5x2 (r2, r);
      s_r2r <- r2r;
      i <- 0;
      while (i < 4) {
        t_u128 <- x86_VPMULU_128 r2r.[(i + 1)] five_u128;
        s_r2rx5.[i] <- t_u128;
        i <- i + 1;
      }
      r2r2 <@ unpack_u26x5x2_to_u26x5x2 (r2, r2);
      s_r2r2 <- r2r2;
      i <- 0;
      while (i < 4) {
        t_u128 <- x86_VPMULU_128 r2r2.[(i + 1)] five_u128;
        s_r2r2x5.[i] <- t_u128;
        i <- i + 1;
      }
      b64 <- s_b64;
      if (((W64.of_uint 1) \ult b64)) {
        r4 <- r2;
        r4 <@ mulmod_12 (r4, s_r2, s_r2x5);
        r4 <@ carry_reduce (r4);
        r4r4 <@ unpack_u26x5x2_to_u26x5x2 (r4, r4);
        s_r4r4 <- r4r4;
        i <- 0;
        while (i < 4) {
          t_u128 <- x86_VPMULU_128 r4r4.[(i + 1)] five_u128;
          s_r4r4x5.[i] <- t_u128;
          i <- i + 1;
        }
      } else {
        
      }
      in_0 <- s_in;
      (hxy, in_0) <@ first_block (in_0, s_r2r2, s_r2r2x5);
      b64 <- s_b64;
      b64 <- (b64 - (W64.of_uint 1));
      
      while (((W64.of_uint 0) \ult b64)) {
        b64 <- (b64 - (W64.of_uint 1));
        s_b64 <- b64;
        (hxy, in_0) <@ remaining_blocks (hxy, in_0, s_r4r4, s_r4r4x5, s_r2r2,
        s_r2r2x5);
        b64 <- s_b64;
      }
      h <@ final_mul (hxy, s_r2r, s_r2rx5);
    } else {
      
    }
    b16 <- s_inlen;
    b16 <- (b16 `>>` (W8.of_uint 4));
    b16 <- (b16 `&` (W64.of_uint 3));
    
    while (((W64.of_uint 0) \ult b16)) {
      b16 <- (b16 - (W64.of_uint 1));
      x <@ load (in_0);
      in_0 <- (in_0 + (W64.of_uint 16));
      h <@ add (h, x);
      h <@ mulmod_12 (h, s_r, s_rx5);
      h <@ carry_reduce (h);
    }
    inlen <- s_inlen;
    inlen <- (inlen `&` (W64.of_uint 15));
    if ((inlen <> (W64.of_uint 0))) {
      x <@ load_last (in_0, inlen);
      h <@ add (h, x);
      h <@ mulmod_12 (h, s_r, s_rx5);
      h <@ carry_reduce (h);
    } else {
      
    }
    h <@ freeze (h);
    k <- s_k;
    k <- (k + (W64.of_uint 16));
    out <- s_out;
    s <@ unpack (k);
    h <@ add_carry (h, s);
    pack (out, h);
    return ();
  }
}.

