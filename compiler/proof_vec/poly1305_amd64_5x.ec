require import Jasmin_model Int IntDiv CoreMap.



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
  
  proc mulmod_add_12 (u:(int,W64.t)map, x:(int,W64.t)map, y:(int,W64.t)map,
                      yx5:(int,W64.t)map) : (int,W64.t)map = {
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
    t <@ add (t, u);
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
    u.[0] <- t.[0];
    u.[0] <- (u.[0] + z.[0]);
    z.[0] <- x.[4];
    z.[0] <- (z.[0] * yx5.[3]);
    u.[1] <- t.[1];
    u.[1] <- (u.[1] + z.[1]);
    u.[2] <- t.[2];
    u.[2] <- (u.[2] + z.[2]);
    u.[3] <- t.[3];
    u.[3] <- (u.[3] + z.[0]);
    u.[4] <- t.[4];
    return (u);
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
                                               s_r2:(int,W64.t)map,
                                               s_r2x5:(int,W64.t)map) : 
  (int,W64.t)map * (int,W64.t)map * W64.t = {
    var hx:(int,W64.t)map;
    var hy:(int,W64.t)map;
    var x0:(int,W64.t)map;
    var x1:(int,W64.t)map;
    var i:int;
    var s_hx:(int,W64.t)map;
    var y0:(int,W64.t)map;
    var y1:(int,W64.t)map;
    var i_0:int;
    hx <- (array_init_64 5);
    hy <- (array_init_64 5);
    s_hx <- (array_init_64 5);
    x0 <- (array_init_64 5);
    x1 <- (array_init_64 5);
    y0 <- (array_init_64 5);
    y1 <- (array_init_64 5);
    x0 <@ load (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hx <@ mulmod_12 (x0, s_r2, s_r2x5);
    x1 <@ load (global_mem, in_0);
    in_0 <- (in_0 - (W64.of_int 16));
    hx <@ add (hx, x1);
    hx <@ carry_reduce (hx);
    i <- 0;
    while (i < 5) {
      s_hx.[i] <- hx.[i];
      i <- i + 1;
    }
    y0 <@ load (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hy <@ mulmod_12 (y0, s_r2, s_r2x5);
    y1 <@ load (global_mem, in_0);
    hy <@ add (hy, y1);
    hy <@ carry_reduce (hy);
    in_0 <- (in_0 + (W64.of_int 16));
    i_0 <- 0;
    while (i_0 < 5) {
      hx.[i_0] <- s_hx.[i_0];
      i_0 <- i_0 + 1;
    }
    return (hx, hy, in_0);
  }
  
  proc remaining_blocks (global_mem : global_mem_t, hx:(int,W64.t)map,
                                                    hy:(int,W64.t)map,
                                                    in_0:W64.t,
                                                    s_r4:(int,W64.t)map,
                                                    s_r4x5:(int,W64.t)map,
                                                    s_r2:(int,W64.t)map,
                                                    s_r2x5:(int,W64.t)map) : 
  (int,W64.t)map * (int,W64.t)map * W64.t = {
    var i:int;
    var s_hy:(int,W64.t)map;
    var x0:(int,W64.t)map;
    var x1:(int,W64.t)map;
    var i_0:int;
    var s_hx:(int,W64.t)map;
    var i_1:int;
    var y0:(int,W64.t)map;
    var y1:(int,W64.t)map;
    s_hx <- (array_init_64 5);
    s_hy <- (array_init_64 5);
    x0 <- (array_init_64 5);
    x1 <- (array_init_64 5);
    y0 <- (array_init_64 5);
    y1 <- (array_init_64 5);
    i <- 0;
    while (i < 5) {
      s_hy.[i] <- hy.[i];
      i <- i + 1;
    }
    hx <@ mulmod_12 (hx, s_r4, s_r4x5);
    x0 <@ load (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hx <@ mulmod_add_12 (hx, x0, s_r2, s_r2x5);
    x1 <@ load (global_mem, in_0);
    in_0 <- (in_0 - (W64.of_int 16));
    hx <@ add (hx, x1);
    hx <@ carry_reduce (hx);
    i_0 <- 0;
    while (i_0 < 5) {
      s_hx.[i_0] <- hx.[i_0];
      i_0 <- i_0 + 1;
    }
    i_1 <- 0;
    while (i_1 < 5) {
      hy.[i_1] <- s_hy.[i_1];
      i_1 <- i_1 + 1;
    }
    hy <@ mulmod_12 (hy, s_r4, s_r4x5);
    y0 <@ load (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 32));
    hy <@ mulmod_add_12 (hy, y0, s_r2, s_r2x5);
    y1 <@ load (global_mem, in_0);
    in_0 <- (in_0 + (W64.of_int 16));
    hy <@ add (hy, y1);
    hy <@ carry_reduce (hy);
    i_1 <- 0;
    while (i_1 < 5) {
      hx.[i_1] <- s_hx.[i_1];
      i_1 <- i_1 + 1;
    }
    return (hx, hy, in_0);
  }
  
  proc final_mul (hx:(int,W64.t)map, hy:(int,W64.t)map, s_r2:(int,W64.t)map,
                  s_r2x5:(int,W64.t)map, s_r:(int,W64.t)map,
                  s_rx5:(int,W64.t)map) : (int,W64.t)map = {
    var h:(int,W64.t)map;
    var i:int;
    var s_hy:(int,W64.t)map;
    var i_0:int;
    var s_hx:(int,W64.t)map;
    var i_1:int;
    h <- (array_init_64 5);
    s_hx <- (array_init_64 5);
    s_hy <- (array_init_64 5);
    i <- 0;
    while (i < 5) {
      s_hy.[i] <- hy.[i];
      i <- i + 1;
    }
    hx <@ mulmod_12 (hx, s_r2, s_r2x5);
    hx <@ carry_reduce (hx);
    i_0 <- 0;
    while (i_0 < 5) {
      s_hx.[i_0] <- hx.[i_0];
      i_0 <- i_0 + 1;
    }
    i_1 <- 0;
    while (i_1 < 5) {
      hy.[i_1] <- s_hy.[i_1];
      i_1 <- i_1 + 1;
    }
    hy <@ mulmod_12 (hy, s_r, s_rx5);
    hy <@ carry_reduce (hy);
    i_1 <- 0;
    while (i_1 < 5) {
      hx.[i_1] <- s_hx.[i_1];
      i_1 <- i_1 + 1;
    }
    h <@ add_carry (hx, hy);
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
    var i_3:int;
    var r4:(int,W64.t)map;
    var i_4:int;
    var s_r4:(int,W64.t)map;
    var s_r4x5:(int,W64.t)map;
    var hx:(int,W64.t)map;
    var hy:(int,W64.t)map;
    var b16:W64.t;
    var x:(int,W64.t)map;
    var s:(int,W64.t)map;
    h <- (array_init_64 5);
    hx <- (array_init_64 5);
    hy <- (array_init_64 5);
    r <- (array_init_64 5);
    r2 <- (array_init_64 5);
    r4 <- (array_init_64 5);
    s <- (array_init_64 5);
    s_r <- (array_init_64 5);
    s_r2 <- (array_init_64 5);
    s_r2x5 <- (array_init_64 4);
    s_r4 <- (array_init_64 5);
    s_r4x5 <- (array_init_64 4);
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
      b64 <- s_b64;
      if (((W64.of_int 1) `<` b64)) {
        i_3 <- 0;
        while (i_3 < 5) {
          r4.[i_3] <- r2.[i_3];
          i_3 <- i_3 + 1;
        }
        r4 <@ mulmod_12 (r4, s_r2, s_r2x5);
        r4 <@ carry_reduce (r4);
        i_4 <- 0;
        while (i_4 < 5) {
          s_r4.[i_4] <- r4.[i_4];
          i_4 <- i_4 + 1;
        }
        i_0 <- 0;
        while (i_0 < 4) {
          t <- (r4.[(i_0 + 1)] * (W64.of_int 5));
          s_r4x5.[i_0] <- t;
          i_0 <- i_0 + 1;
        }
      } else {
        
      }
      in_0 <- s_in;
      (hx, hy, in_0) <@ first_block (global_mem, in_0, s_r2, s_r2x5);
      b64 <- s_b64;
      b64 <- (b64 - (W64.of_int 1));
      
      while (((W64.of_int 0) `<` b64)) {
        b64 <- (b64 - (W64.of_int 1));
        s_b64 <- b64;
        (hx, hy, in_0) <@ remaining_blocks (global_mem, hx, hy, in_0, s_r4,
        s_r4x5, s_r2, s_r2x5);
        b64 <- s_b64;
      }
      h <@ final_mul (hx, hy, s_r2, s_r2x5, s_r, s_rx5);
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

