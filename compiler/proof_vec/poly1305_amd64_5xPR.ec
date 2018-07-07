require import List Jasmin_model Int IntDiv CoreMap.




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
  
  proc mulmod_add_12 (u:W64.t Array5.t, x:W64.t Array5.t, y:W64.t Array5.t,
                      yx5:W64.t Array4.t) : W64.t Array5.t = {
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
  
  proc mulmod_u128 (x1:W64.t Array5.t, x2:W64.t Array5.t, y1:W64.t Array5.t,
                    y1x5:W64.t Array4.t, y2:W64.t Array5.t,
                    y2x5:W64.t Array4.t) : W64.t Array5.t * W64.t Array5.t = {
    
    
    x1 <@ mulmod_12 (x1, y1, y1x5);
    x2 <@ mulmod_12 (x2, y2, y2x5);
    return (x1, x2);
  }
  
  proc mulmod_add_u128 (u1:W64.t Array5.t, u2:W64.t Array5.t,
                        x1:W64.t Array5.t, x2:W64.t Array5.t,
                        y:W64.t Array5.t, yx5:W64.t Array4.t) : W64.t Array5.t *
                                                                W64.t Array5.t = {
    
    
    u1 <@ mulmod_add_12 (u1, x1, y, yx5);
    u2 <@ mulmod_add_12 (u2, x2, y, yx5);
    return (u1, u2);
  }
  
  proc add_u128 (x1:W64.t Array5.t, x2:W64.t Array5.t, y1:W64.t Array5.t,
                 y2:W64.t Array5.t) : W64.t Array5.t * W64.t Array5.t = {
    
    
    x1 <@ add (x1, y1);
    x2 <@ add (x2, y2);
    return (x1, x2);
  }
  
  proc unpack_u128x2_to_u26x5x2 (in_0:W64.t) : W64.t Array5.t *
                                               W64.t Array5.t = {
    var x:W64.t Array5.t;
    var y:W64.t Array5.t;
    x <- Array5.init W64.zeros;
    y <- Array5.init W64.zeros;
    x <@ load (in_0);
    in_0 <- (in_0 + (W64.of_uint 16));
    y <@ load (in_0);
    return (x, y);
  }
  
  proc carry_reduce_u128 (hx:W64.t Array5.t, hy:W64.t Array5.t) : W64.t Array5.t *
                                                                  W64.t Array5.t = {
    
    
    hx <@ carry_reduce (hx);
    hy <@ carry_reduce (hy);
    return (hx, hy);
  }
  
  proc first_block (in_0:W64.t, s_r2:W64.t Array5.t, s_r2x5:W64.t Array4.t) : 
  W64.t Array5.t * W64.t Array5.t * W64.t = {
    var hx:W64.t Array5.t;
    var hy:W64.t Array5.t;
    var x0:W64.t Array5.t;
    var y0:W64.t Array5.t;
    var x1:W64.t Array5.t;
    var y1:W64.t Array5.t;
    hx <- Array5.init W64.zeros;
    hy <- Array5.init W64.zeros;
    x0 <- Array5.init W64.zeros;
    x1 <- Array5.init W64.zeros;
    y0 <- Array5.init W64.zeros;
    y1 <- Array5.init W64.zeros;
    (x0, y0) <@ unpack_u128x2_to_u26x5x2 (in_0);
    in_0 <- (in_0 + (W64.of_uint 32));
    (hx, hy) <@ mulmod_u128 (x0, y0, s_r2, s_r2x5, s_r2, s_r2x5);
    (x1, y1) <@ unpack_u128x2_to_u26x5x2 (in_0);
    in_0 <- (in_0 + (W64.of_uint 32));
    (hx, hy) <@ add_u128 (hx, hy, x1, y1);
    (hx, hy) <@ carry_reduce_u128 (hx, hy);
    return (hx, hy, in_0);
  }
  
  proc remaining_blocks (hx:W64.t Array5.t, hy:W64.t Array5.t, in_0:W64.t,
                         s_r4:W64.t Array5.t, s_r4x5:W64.t Array4.t,
                         s_r2:W64.t Array5.t, s_r2x5:W64.t Array4.t) : 
  W64.t Array5.t * W64.t Array5.t * W64.t = {
    var x0:W64.t Array5.t;
    var y0:W64.t Array5.t;
    var x1:W64.t Array5.t;
    var y1:W64.t Array5.t;
    x0 <- Array5.init W64.zeros;
    x1 <- Array5.init W64.zeros;
    y0 <- Array5.init W64.zeros;
    y1 <- Array5.init W64.zeros;
    (hx, hy) <@ mulmod_u128 (hx, hy, s_r4, s_r4x5, s_r4, s_r4x5);
    (x0, y0) <@ unpack_u128x2_to_u26x5x2 (in_0);
    in_0 <- (in_0 + (W64.of_uint 32));
    (hx, hy) <@ mulmod_add_u128 (hx, hy, x0, y0, s_r2, s_r2x5);
    (x1, y1) <@ unpack_u128x2_to_u26x5x2 (in_0);
    in_0 <- (in_0 + (W64.of_uint 32));
    (hx, hy) <@ add_u128 (hx, hy, x1, y1);
    (hx, hy) <@ carry_reduce_u128 (hx, hy);
    return (hx, hy, in_0);
  }
  
  proc final_mul (hx:W64.t Array5.t, hy:W64.t Array5.t, s_r2:W64.t Array5.t,
                  s_r2x5:W64.t Array4.t, s_r:W64.t Array5.t,
                  s_rx5:W64.t Array4.t) : W64.t Array5.t = {
    var h:W64.t Array5.t;
    h <- Array5.init W64.zeros;
    (hx, hy) <@ mulmod_u128 (hx, hy, s_r2, s_r2x5, s_r, s_rx5);
    (hx, hy) <@ carry_reduce_u128 (hx, hy);
    h <@ add_carry (hx, hy);
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
    var r4:W64.t Array5.t;
    var s_r4:W64.t Array5.t;
    var s_r4x5:W64.t Array4.t;
    var hx:W64.t Array5.t;
    var hy:W64.t Array5.t;
    var b16:W64.t;
    var x:W64.t Array5.t;
    var s:W64.t Array5.t;
    h <- Array5.init W64.zeros;
    hx <- Array5.init W64.zeros;
    hy <- Array5.init W64.zeros;
    r <- Array5.init W64.zeros;
    r2 <- Array5.init W64.zeros;
    r4 <- Array5.init W64.zeros;
    s <- Array5.init W64.zeros;
    s_r <- Array5.init W64.zeros;
    s_r2 <- Array5.init W64.zeros;
    s_r2x5 <- Array4.init W64.zeros;
    s_r4 <- Array5.init W64.zeros;
    s_r4x5 <- Array4.init W64.zeros;
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
      b64 <- s_b64;
      if (((W64.of_uint 1) \ult b64)) {
        r4 <- r2;
        r4 <@ mulmod_12 (r4, s_r2, s_r2x5);
        r4 <@ carry_reduce (r4);
        s_r4 <- r4;
        i <- 0;
        while (i < 4) {
          t <- (r4.[(i + 1)] * (W64.of_uint 5));
          s_r4x5.[i] <- t;
          i <- i + 1;
        }
      } else {
        
      }
      in_0 <- s_in;
      (hx, hy, in_0) <@ first_block (in_0, s_r2, s_r2x5);
      b64 <- s_b64;
      b64 <- (b64 - (W64.of_uint 1));
      
      while (((W64.of_uint 0) \ult b64)) {
        b64 <- (b64 - (W64.of_uint 1));
        s_b64 <- b64;
        (hx, hy, in_0) <@ remaining_blocks (hx, hy, in_0, s_r4, s_r4x5, s_r2,
        s_r2x5);
        b64 <- s_b64;
      }
      h <@ final_mul (hx, hy, s_r2, s_r2x5, s_r, s_rx5);
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

