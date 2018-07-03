require import Jasmin_model Int IntDiv CoreMap.

abbrev zero_u128 = W128.of_int 0.


abbrev five_u128 = W128.of_int 92233720368547758085.


abbrev bit25_u128 = W128.of_int 309485009821345068741558272.


abbrev mask26_u128 = W128.of_int 1237940020838636201256681471.


module M = {
  proc add (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    var i:int;
    
    i <- 0;
    while (i < 5) {
      x.[i] <- (x.[i] + y.[i]);
      i <- i + 1;
    }
    return (x);
  }
  
  proc add_carry (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    var i:int;
    var c:W64.t;
    
    x.[0] <- (x.[0] + y.[0]);
    i <- 0;
    while (i < 4) {
      c <- x.[i];
      c <- (c `>>` (W8.of_int 26));
      x.[i] <- (x.[i] `&` (W64.of_int 67108863));
      x.[(i + 1)] <- (x.[(i + 1)] + y.[(i + 1)]);
      x.[(i + 1)] <- (x.[(i + 1)] + c);
      i <- i + 1;
    }
    return (x);
  }
  
  proc add_u128 (x:(int,W128.t)map, y:(int,W128.t)map) : (int,W128.t)map = {
    var i:int;
    
    i <- 0;
    while (i < 5) {
      x.[i] <- x86_VPADD_2u64 x.[i] y.[i];
      i <- i + 1;
    }
    return (x);
  }
  
  proc hadd_u128 (x:(int,W128.t)map) : (int,W64.t)map = {
    var h:(int,W64.t)map;
    var i:int;
    var t:(int,W64.t)map;
    h <- (array_init_64 5);
    t <- (array_init_64 5);
    i <- 0;
    while (i < 5) {
      t.[i] <- x86_VPEXTR_64 x.[i] (W8.of_int 0);
      h.[i] <- x86_VPEXTR_64 x.[i] (W8.of_int 1);
      i <- i + 1;
    }
    h <@ add_carry (h, t);
    return (h);
  }
  
  proc freeze (x:(int,W64.t)map) : (int,W64.t)map = {
    var i:int;
    var ox:(int,W64.t)map;
    var mp:(int,W64.t)map;
    var n:W64.t;
    mp <- (array_init_64 5);
    ox <- (array_init_64 5);
    i <- 0;
    while (i < 5) {
      ox.[i] <- x.[i];
      i <- i + 1;
    }
    mp.[0] <- (W64.of_int 5);
    mp.[1] <- (W64.of_int 0);
    mp.[2] <- (W64.of_int 0);
    mp.[3] <- (W64.of_int 0);
    mp.[4] <- (W64.of_int 67108864);
    x <@ add_carry (x, mp);
    n <- x.[4];
    n <- (n `>>` (W8.of_int 26));
    n <- (n `&` (W64.of_int 1));
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
  
  proc unpack (global_mem : global_mem_t, m:W64.t) : (int,W64.t)map = {
    var x:(int,W64.t)map;
    var m0:W64.t;
    var m1:W64.t;
    var t:W64.t;
    x <- (array_init_64 5);
    m0 <- (loadW64 global_mem (m + (W64.of_int (8 * 0))));
    m1 <- (loadW64 global_mem (m + (W64.of_int (8 * 1))));
    x.[0] <- m0;
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    m0 <- (m0 `>>` (W8.of_int 26));
    x.[1] <- m0;
    x.[1] <- (x.[1] `&` (W64.of_int 67108863));
    m0 <- (m0 `>>` (W8.of_int 26));
    x.[2] <- m0;
    t <- m1;
    t <- (t `<<` (W8.of_int 12));
    x.[2] <- (x.[2] `|` t);
    x.[2] <- (x.[2] `&` (W64.of_int 67108863));
    m1 <- (m1 `>>` (W8.of_int 14));
    x.[3] <- m1;
    x.[3] <- (x.[3] `&` (W64.of_int 67108863));
    m1 <- (m1 `>>` (W8.of_int 26));
    x.[4] <- m1;
    return (x);
  }
  
  proc mulmod_12 (x:(int,W64.t)map, y:(int,W64.t)map, yx5:(int,W64.t)map) : 
  (int,W64.t)map = {
    var t:(int,W64.t)map;
    var z:(int,W64.t)map;
    t <- (array_init_64 5);
    z <- (array_init_64 3);
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
  
  proc carry_reduce (x:(int,W64.t)map) : (int,W64.t)map = {
    var z:(int,W64.t)map;
    z <- (array_init_64 2);
    z.[0] <- x.[0];
    z.[0] <- (z.[0] `>>` (W8.of_int 26));
    z.[1] <- x.[3];
    z.[1] <- (z.[1] `>>` (W8.of_int 26));
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    x.[3] <- (x.[3] `&` (W64.of_int 67108863));
    x.[1] <- (x.[1] + z.[0]);
    x.[4] <- (x.[4] + z.[1]);
    z.[0] <- x.[1];
    z.[0] <- (z.[0] `>>` (W8.of_int 26));
    z.[1] <- x.[4];
    z.[1] <- (z.[1] `>>` (W8.of_int 26));
    z.[1] <- (z.[1] * (W64.of_int 5));
    x.[1] <- (x.[1] `&` (W64.of_int 67108863));
    x.[4] <- (x.[4] `&` (W64.of_int 67108863));
    x.[2] <- (x.[2] + z.[0]);
    x.[0] <- (x.[0] + z.[1]);
    z.[0] <- x.[2];
    z.[0] <- (z.[0] `>>` (W8.of_int 26));
    z.[1] <- x.[0];
    z.[1] <- (z.[1] `>>` (W8.of_int 26));
    x.[2] <- (x.[2] `&` (W64.of_int 67108863));
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    x.[3] <- (x.[3] + z.[0]);
    x.[1] <- (x.[1] + z.[1]);
    z.[0] <- x.[3];
    z.[0] <- (z.[0] `>>` (W8.of_int 26));
    x.[3] <- (x.[3] `&` (W64.of_int 67108863));
    x.[4] <- (x.[4] + z.[0]);
    return (x);
  }
  
  proc unpack_u26x5x2_to_u26x5x2 (s:(int,W64.t)map, t:(int,W64.t)map) : 
  (int,W128.t)map = {
    var r:(int,W128.t)map;
    var i:int;
    r <- (array_init_128 5);
    i <- 0;
    while (i < 5) {
      r.[i] <- zero_u128;
      r.[i] <- x86_VPINSR_2u64 r.[i] s.[i] (W8.of_int 0);
      r.[i] <- x86_VPINSR_2u64 r.[i] t.[i] (W8.of_int 1);
      i <- i + 1;
    }
    return (r);
  }
  
  proc unpack_u128x2_to_u26x5x2 (global_mem : global_mem_t, m:W64.t) : 
  (int,W128.t)map = {
    var r:(int,W128.t)map;
    var s128:W128.t;
    var t128:W128.t;
    var t1:W128.t;
    var t2:W128.t;
    var t3:W128.t;
    r <- (array_init_128 5);
    s128 <- x86_MOVD_64 (loadW64 global_mem (m + (W64.of_int (8 * 0))));
    t128 <- x86_MOVD_64 (loadW64 global_mem (m + (W64.of_int (8 * 2))));
    t1 <- x86_VPUNPCKL_2u64 s128 t128;
    s128 <- x86_MOVD_64 (loadW64 global_mem (m + (W64.of_int (8 * 1))));
    t128 <- x86_MOVD_64 (loadW64 global_mem (m + (W64.of_int (8 * 3))));
    t2 <- x86_VPUNPCKL_2u64 s128 t128;
    t3 <- x86_VPSLL_2u64 t2 (W8.of_int 12);
    r.[0] <- x86_VPAND_128 t1 mask26_u128;
    t1 <- x86_VPSRL_2u64 t1 (W8.of_int 26);
    r.[1] <- x86_VPAND_128 t1 mask26_u128;
    t1 <- x86_VPSRL_2u64 t1 (W8.of_int 26);
    t1 <- x86_VPOR_128 t1 t3;
    r.[2] <- x86_VPAND_128 t1 mask26_u128;
    t1 <- x86_VPSRL_2u64 t1 (W8.of_int 26);
    r.[3] <- x86_VPAND_128 t1 mask26_u128;
    r.[4] <- x86_VPSRL_2u64 t2 (W8.of_int 40);
    r.[4] <- x86_VPOR_128 r.[4] bit25_u128;
    return (r);
  }
  
  proc mulmod_u128 (x:(int,W128.t)map, y:(int,W128.t)map, yx5:(int,W128.t)map) : 
  (int,W128.t)map = {
    var t:(int,W128.t)map;
    var z:(int,W128.t)map;
    t <- (array_init_128 5);
    z <- (array_init_128 5);
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
  
  proc mulmod_add_u128 (u:(int,W128.t)map, x:(int,W128.t)map,
                        y:(int,W128.t)map, yx5:(int,W128.t)map) : (int,W128.t)map = {
    var t:(int,W128.t)map;
    var z:(int,W128.t)map;
    t <- (array_init_128 5);
    z <- (array_init_128 5);
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
    t.[2] <- x86_VPADD_2u64 t.[2] z.[0];
    u.[0] <- x86_VPADD_2u64 t.[0] z.[1];
    u.[1] <- x86_VPADD_2u64 t.[1] z.[2];
    u.[2] <- x86_VPADD_2u64 t.[2] z.[3];
    u.[3] <- x86_VPADD_2u64 t.[3] z.[4];
    u.[4] <- t.[4];
    return (u);
  }
  
  proc carry_reduce_u128 (x:(int,W128.t)map) : (int,W128.t)map = {
    var z:(int,W128.t)map;
    z <- (array_init_128 2);
    z.[0] <- x86_VPSRL_2u64 x.[0] (W8.of_int 26);
    z.[1] <- x86_VPSRL_2u64 x.[3] (W8.of_int 26);
    x.[0] <- x86_VPAND_128 x.[0] mask26_u128;
    x.[3] <- x86_VPAND_128 x.[3] mask26_u128;
    x.[1] <- x86_VPADD_2u64 x.[1] z.[0];
    x.[4] <- x86_VPADD_2u64 x.[4] z.[1];
    z.[0] <- x86_VPSRL_2u64 x.[1] (W8.of_int 26);
    z.[1] <- x86_VPSRL_2u64 x.[4] (W8.of_int 26);
    z.[1] <- x86_VPMULU_128 z.[1] five_u128;
    x.[1] <- x86_VPAND_128 x.[1] mask26_u128;
    x.[4] <- x86_VPAND_128 x.[4] mask26_u128;
    x.[2] <- x86_VPADD_2u64 x.[2] z.[0];
    x.[0] <- x86_VPADD_2u64 x.[0] z.[1];
    z.[0] <- x86_VPSRL_2u64 x.[2] (W8.of_int 26);
    z.[1] <- x86_VPSRL_2u64 x.[0] (W8.of_int 26);
    x.[2] <- x86_VPAND_128 x.[2] mask26_u128;
    x.[0] <- x86_VPAND_128 x.[0] mask26_u128;
    x.[3] <- x86_VPADD_2u64 x.[3] z.[0];
    x.[1] <- x86_VPADD_2u64 x.[1] z.[1];
    z.[0] <- x86_VPSRL_2u64 x.[3] (W8.of_int 26);
    x.[3] <- x86_VPAND_128 x.[3] mask26_u128;
    x.[4] <- x86_VPADD_2u64 x.[4] z.[0];
    return (x);
  }
  
  proc clamp (global_mem : global_mem_t, k:W64.t) : (int,W64.t)map = {
    var r:(int,W64.t)map;
    r <- (array_init_64 5);
    r <@ unpack (global_mem, k);
    r.[0] <- (r.[0] `&` (W64.of_int 67108863));
    r.[1] <- (r.[1] `&` (W64.of_int 67108611));
    r.[2] <- (r.[2] `&` (W64.of_int 67092735));
    r.[3] <- (r.[3] `&` (W64.of_int 66076671));
    r.[4] <- (r.[4] `&` (W64.of_int 1048575));
    return (r);
  }
  
  proc load (global_mem : global_mem_t, in_0:W64.t) : (int,W64.t)map = {
    var x:(int,W64.t)map;
    x <- (array_init_64 5);
    x <@ unpack (global_mem, in_0);
    x.[4] <- (x.[4] `|` (W64.of_int 16777216));
    return (x);
  }
  
  proc load_last (global_mem : global_mem_t, in_0:W64.t, inlen:W64.t) : 
  (int,W64.t)map = {
    var x:(int,W64.t)map;
    var i:int;
    var m:(int,W64.t)map;
    var c:W64.t;
    var n:W64.t;
    var t:W64.t;
    m <- (array_init_64 2);
    x <- (array_init_64 5);
    i <- 0;
    while (i < 2) {
      m.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    if ((inlen `<` (W64.of_int 8))) {
      c <- (W64.of_int 0);
      n <- (W64.of_int 0);
      
      while ((c `<` inlen)) {
        t <- (zeroext_8_64 (loadW8 global_mem (in_0 + c)));
        t <- (t `<<` (zeroext_64_8 n));
        m.[0] <- (m.[0] `|` t);
        n <- (n + (W64.of_int 8));
        c <- (c + (W64.of_int 1));
      }
      t <- (W64.of_int 1);
      t <- (t `<<` (zeroext_64_8 n));
      m.[0] <- (m.[0] `|` t);
    } else {
      m.[0] <- (loadW64 global_mem (in_0 + (W64.of_int 0)));
      inlen <- (inlen - (W64.of_int 8));
      in_0 <- (in_0 + (W64.of_int 8));
      c <- (W64.of_int 0);
      n <- (W64.of_int 0);
      
      while ((c `<` inlen)) {
        t <- (zeroext_8_64 (loadW8 global_mem (in_0 + c)));
        t <- (t `<<` (zeroext_64_8 n));
        m.[1] <- (m.[1] `|` t);
        n <- (n + (W64.of_int 8));
        c <- (c + (W64.of_int 1));
      }
      t <- (W64.of_int 1);
      t <- (t `<<` (zeroext_64_8 n));
      m.[1] <- (m.[1] `|` t);
    }
    x.[0] <- m.[0];
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    m.[0] <- (m.[0] `>>` (W8.of_int 26));
    x.[1] <- m.[0];
    x.[1] <- (x.[1] `&` (W64.of_int 67108863));
    m.[0] <- (m.[0] `>>` (W8.of_int 26));
    x.[2] <- m.[0];
    t <- m.[1];
    t <- (t `<<` (W8.of_int 12));
    x.[2] <- (x.[2] `|` t);
    x.[2] <- (x.[2] `&` (W64.of_int 67108863));
    m.[1] <- (m.[1] `>>` (W8.of_int 14));
    x.[3] <- m.[1];
    x.[3] <- (x.[3] `&` (W64.of_int 67108863));
    m.[1] <- (m.[1] `>>` (W8.of_int 26));
    x.[4] <- m.[1];
    return (x);
  }
  
  proc pack (global_mem : global_mem_t, y:W64.t, x:(int,W64.t)map) : 
  global_mem_t = {
    var t:W64.t;
    var t1:W64.t;
    
    t <- x.[0];
    t1 <- x.[1];
    t1 <- (t1 `<<` (W8.of_int 26));
    t <- (t `|` t1);
    t1 <- x.[2];
    t1 <- (t1 `<<` (W8.of_int 52));
    t <- (t `|` t1);
    global_mem <- storeW64 global_mem (y + (W64.of_int (0 * 8))) t;
    t <- x.[2];
    t <- (t `&` (W64.of_int 67108863));
    t <- (t `>>` (W8.of_int 12));
    t1 <- x.[3];
    t1 <- (t1 `<<` (W8.of_int 14));
    t <- (t `|` t1);
    t1 <- x.[4];
    t1 <- (t1 `<<` (W8.of_int 40));
    t <- (t `|` t1);
    global_mem <- storeW64 global_mem (y + (W64.of_int (1 * 8))) t;
    return global_mem;
  }
  
  proc first_block (global_mem : global_mem_t, in_0:W64.t,
                                               s_r2r2:(int,W128.t)map,
                                               s_r2r2x5:(int,W128.t)map) : 
  (int,W128.t)map * W64.t = {
    var hxy:(int,W128.t)map;
    var xy0:(int,W128.t)map;
    var xy1:(int,W128.t)map;
    hxy <- (array_init_128 5);
    xy0 <- (array_init_128 5);
    xy1 <- (array_init_128 5);
    xy0 <@ unpack_u128x2_to_u26x5x2 (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hxy <@ mulmod_u128 (xy0, s_r2r2, s_r2r2x5);
    xy1 <@ unpack_u128x2_to_u26x5x2 (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hxy <@ add_u128 (hxy, xy1);
    hxy <@ carry_reduce_u128 (hxy);
    return (hxy, in_0);
  }
  
  proc remaining_blocks (global_mem : global_mem_t, hxy:(int,W128.t)map,
                                                    in_0:W64.t,
                                                    s_r4r4:(int,W128.t)map,
                                                    s_r4r4x5:(int,W128.t)map,
                                                    s_r2r2:(int,W128.t)map,
                                                    s_r2r2x5:(int,W128.t)map) : 
  (int,W128.t)map * W64.t = {
    var xy0:(int,W128.t)map;
    var xy1:(int,W128.t)map;
    xy0 <- (array_init_128 5);
    xy1 <- (array_init_128 5);
    hxy <@ mulmod_u128 (hxy, s_r4r4, s_r4r4x5);
    xy0 <@ unpack_u128x2_to_u26x5x2 (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hxy <@ mulmod_add_u128 (hxy, xy0, s_r2r2, s_r2r2x5);
    xy1 <@ unpack_u128x2_to_u26x5x2 (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hxy <@ add_u128 (hxy, xy1);
    hxy <@ carry_reduce_u128 (hxy);
    return (hxy, in_0);
  }
  
  proc final_mul (hxy:(int,W128.t)map, s_r2r:(int,W128.t)map,
                  s_r2rx5:(int,W128.t)map) : (int,W64.t)map = {
    var h:(int,W64.t)map;
    h <- (array_init_64 5);
    hxy <@ mulmod_u128 (hxy, s_r2r, s_r2rx5);
    hxy <@ carry_reduce_u128 (hxy);
    h <@ hadd_u128 (hxy);
    return (h);
  }
  
  proc poly1305 (global_mem : global_mem_t, out:W64.t, in_0:W64.t,
                                            inlen:W64.t, k:W64.t) : global_mem_t = {
    var s_out:W64.t;
    var s_in:W64.t;
    var s_inlen:W64.t;
    var s_k:W64.t;
    var r:(int,W64.t)map;
    var i:int;
    var s_r:(int,W64.t)map;
    var i_0:int;
    var t:W64.t;
    var s_rx5:(int,W64.t)map;
    var h:(int,W64.t)map;
    var b64:W64.t;
    var s_b64:W64.t;
    var i_1:int;
    var r2:(int,W64.t)map;
    var i_2:int;
    var s_r2:(int,W64.t)map;
    var s_r2x5:(int,W64.t)map;
    var r2r:(int,W128.t)map;
    var s_r2r:(int,W128.t)map;
    var t_u128:W128.t;
    var s_r2rx5:(int,W128.t)map;
    var r2r2:(int,W128.t)map;
    var s_r2r2:(int,W128.t)map;
    var s_r2r2x5:(int,W128.t)map;
    var i_3:int;
    var r4:(int,W64.t)map;
    var r4r4:(int,W128.t)map;
    var s_r4r4:(int,W128.t)map;
    var s_r4r4x5:(int,W128.t)map;
    var hxy:(int,W128.t)map;
    var b16:W64.t;
    var x:(int,W64.t)map;
    var s:(int,W64.t)map;
    h <- (array_init_64 5);
    hxy <- (array_init_128 5);
    r <- (array_init_64 5);
    r2 <- (array_init_64 5);
    r2r <- (array_init_128 5);
    r2r2 <- (array_init_128 5);
    r4 <- (array_init_64 5);
    r4r4 <- (array_init_128 5);
    s <- (array_init_64 5);
    s_r <- (array_init_64 5);
    s_r2 <- (array_init_64 5);
    s_r2r <- (array_init_128 5);
    s_r2r2 <- (array_init_128 5);
    s_r2r2x5 <- (array_init_128 4);
    s_r2rx5 <- (array_init_128 4);
    s_r2x5 <- (array_init_64 4);
    s_r4r4 <- (array_init_128 5);
    s_r4r4x5 <- (array_init_128 4);
    s_rx5 <- (array_init_64 4);
    x <- (array_init_64 5);
    s_out <- out;
    s_in <- in_0;
    s_inlen <- inlen;
    s_k <- k;
    r <@ clamp (global_mem, k);
    i <- 0;
    while (i < 5) {
      s_r.[i] <- r.[i];
      i <- i + 1;
    }
    i_0 <- 0;
    while (i_0 < 4) {
      t <- (r.[(i_0 + 1)] * (W64.of_int 5));
      s_rx5.[i_0] <- t;
      i_0 <- i_0 + 1;
    }
    i_0 <- 0;
    while (i_0 < 5) {
      h.[i_0] <- (W64.of_int 0);
      i_0 <- i_0 + 1;
    }
    b64 <- inlen;
    b64 <- (b64 `>>` (W8.of_int 6));
    if (((W64.of_int 0) `<` b64)) {
      s_b64 <- b64;
      i_1 <- 0;
      while (i_1 < 5) {
        r2.[i_1] <- r.[i_1];
        i_1 <- i_1 + 1;
      }
      r2 <@ mulmod_12 (r2, s_r, s_rx5);
      r2 <@ carry_reduce (r2);
      i_2 <- 0;
      while (i_2 < 5) {
        s_r2.[i_2] <- r2.[i_2];
        i_2 <- i_2 + 1;
      }
      i_0 <- 0;
      while (i_0 < 4) {
        t <- (r2.[(i_0 + 1)] * (W64.of_int 5));
        s_r2x5.[i_0] <- t;
        i_0 <- i_0 + 1;
      }
      i_0 <- 0;
      while (i_0 < 5) {
        r.[i_0] <- s_r.[i_0];
        i_0 <- i_0 + 1;
      }
      r2r <@ unpack_u26x5x2_to_u26x5x2 (r2, r);
      i_0 <- 0;
      while (i_0 < 5) {
        s_r2r.[i_0] <- r2r.[i_0];
        i_0 <- i_0 + 1;
      }
      i_0 <- 0;
      while (i_0 < 4) {
        t_u128 <- x86_VPMULU_128 r2r.[(i_0 + 1)] five_u128;
        s_r2rx5.[i_0] <- t_u128;
        i_0 <- i_0 + 1;
      }
      r2r2 <@ unpack_u26x5x2_to_u26x5x2 (r2, r2);
      i_0 <- 0;
      while (i_0 < 5) {
        s_r2r2.[i_0] <- r2r2.[i_0];
        i_0 <- i_0 + 1;
      }
      i_0 <- 0;
      while (i_0 < 4) {
        t_u128 <- x86_VPMULU_128 r2r2.[(i_0 + 1)] five_u128;
        s_r2r2x5.[i_0] <- t_u128;
        i_0 <- i_0 + 1;
      }
      b64 <- s_b64;
      if (((W64.of_int 1) `<` b64)) {
        i_3 <- 0;
        while (i_3 < 5) {
          r4.[i_3] <- r2.[i_3];
          i_3 <- i_3 + 1;
        }
        r4 <@ mulmod_12 (r4, s_r2, s_r2x5);
        r4 <@ carry_reduce (r4);
        r4r4 <@ unpack_u26x5x2_to_u26x5x2 (r4, r4);
        i_0 <- 0;
        while (i_0 < 5) {
          s_r4r4.[i_0] <- r4r4.[i_0];
          i_0 <- i_0 + 1;
        }
        i_0 <- 0;
        while (i_0 < 4) {
          t_u128 <- x86_VPMULU_128 r4r4.[(i_0 + 1)] five_u128;
          s_r4r4x5.[i_0] <- t_u128;
          i_0 <- i_0 + 1;
        }
      } else {
        
      }
      in_0 <- s_in;
      (hxy, in_0) <@ first_block (global_mem, in_0, s_r2r2, s_r2r2x5);
      b64 <- s_b64;
      b64 <- (b64 - (W64.of_int 1));
      
      while (((W64.of_int 0) `<` b64)) {
        b64 <- (b64 - (W64.of_int 1));
        s_b64 <- b64;
        (hxy, in_0) <@ remaining_blocks (global_mem, hxy, in_0, s_r4r4,
        s_r4r4x5, s_r2r2, s_r2r2x5);
        b64 <- s_b64;
      }
      h <@ final_mul (hxy, s_r2r, s_r2rx5);
    } else {
      
    }
    b16 <- s_inlen;
    b16 <- (b16 `>>` (W8.of_int 4));
    b16 <- (b16 `&` (W64.of_int 3));
    
    while (((W64.of_int 0) `<` b16)) {
      b16 <- (b16 - (W64.of_int 1));
      x <@ load (global_mem, in_0);
      in_0 <- (in_0 + (W64.of_int 16));
      h <@ add (h, x);
      h <@ mulmod_12 (h, s_r, s_rx5);
      h <@ carry_reduce (h);
    }
    inlen <- s_inlen;
    inlen <- (inlen `&` (W64.of_int 15));
    if ((inlen <> (W64.of_int 0))) {
      x <@ load_last (global_mem, in_0, inlen);
      h <@ add (h, x);
      h <@ mulmod_12 (h, s_r, s_rx5);
      h <@ carry_reduce (h);
    } else {
      
    }
    h <@ freeze (h);
    k <- s_k;
    k <- (k + (W64.of_int 16));
    out <- s_out;
    s <@ unpack (global_mem, k);
    h <@ add_carry (h, s);
    global_mem <@ pack (global_mem, out, h);
    return global_mem;
  }
}.

