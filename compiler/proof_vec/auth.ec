require import List Jasmin_model Int IntDiv CoreMap.




module M = {
  proc add (x:W64.t Array5.t, y:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 5) {
      x.[i] <- (x.[i] + y.[i]);
      i <- i + 1;
    }
    return (x);
  }
  
  proc add_carry (x:W64.t Array5.t, y:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    
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
  
  proc carry_reduce (x:W64.t Array5.t) : W64.t Array5.t = {
    
    var z:W64.t Array2.t;
    z <- Array2.create W64.zero;
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
  
  proc freeze (x:W64.t Array5.t) : W64.t Array5.t = {
    var aux: int;
    
    var n:W64.t;
    var c:W64.t;
    var ox:W64.t Array5.t;
    var i:int;
    ox <- Array5.create W64.zero;
    n <- x.[4];
    n <- (n `>>` (W8.of_int 26));
    c <- n;
    c <- (c `<<` (W8.of_int 2));
    c <- (c + n);
    x.[0] <- (x.[0] + c);
    ox <- x;
    x.[0] <- (x.[0] + (W64.of_int 5));
    c <- x.[0];
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    c <- (c `>>` (W8.of_int 26));
    i <- 1;
    while (i < 5) {
      x.[i] <- (x.[i] + c);
      c <- x.[i];
      x.[i] <- (x.[i] `&` (W64.of_int 67108863));
      c <- (c `>>` (W8.of_int 26));
      i <- i + 1;
    }
    c <- (c `&` (W64.of_int 1));
    c <- (c - (W64.of_int 1));
    i <- 0;
    while (i < 5) {
      ox.[i] <- (ox.[i] `^` x.[i]);
      i <- i + 1;
    }
    i <- 0;
    while (i < 5) {
      ox.[i] <- (ox.[i] `&` c);
      i <- i + 1;
    }
    i <- 0;
    while (i < 5) {
      x.[i] <- (x.[i] `^` ox.[i]);
      i <- i + 1;
    }
    return (x);
  }
  
  proc unpack (m:W64.t) : W64.t Array5.t = {
    
    var x:W64.t Array5.t;
    var m0:W64.t;
    var m1:W64.t;
    var t:W64.t;
    x <- Array5.create W64.zero;
    m0 <- (loadW64 Glob.mem (m + (W64.of_int (8 * 0))));
    m1 <- (loadW64 Glob.mem (m + (W64.of_int (8 * 1))));
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
  
  proc mulmod (x:W64.t Array5.t, y:W64.t Array5.t, yx5:W64.t Array4.t) : 
  W64.t Array5.t = {
    
    var t:W64.t Array5.t;
    var z:W64.t Array3.t;
    t <- Array5.create W64.zero;
    z <- Array3.create W64.zero;
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
  
  proc clamp (k:W64.t) : W64.t Array5.t = {
    
    var r:W64.t Array5.t;
    r <- Array5.create W64.zero;
    r <@ unpack (k);
    r.[0] <- (r.[0] `&` (W64.of_int 67108863));
    r.[1] <- (r.[1] `&` (W64.of_int 67108611));
    r.[2] <- (r.[2] `&` (W64.of_int 67092735));
    r.[3] <- (r.[3] `&` (W64.of_int 66076671));
    r.[4] <- (r.[4] `&` (W64.of_int 1048575));
    return (r);
  }
  
  proc load (in_0:W64.t) : W64.t Array5.t = {
    
    var x:W64.t Array5.t;
    x <- Array5.create W64.zero;
    x <@ unpack (in_0);
    x.[4] <- (x.[4] `|` (W64.of_int 16777216));
    return (x);
  }
  
  proc load_last (in_0:W64.t, inlen:W64.t) : W64.t Array5.t = {
    var aux: int;
    
    var x:W64.t Array5.t;
    var i:int;
    var m:W64.t Array2.t;
    var c:W64.t;
    var n:W64.t;
    var t:W64.t;
    m <- Array2.create W64.zero;
    x <- Array5.create W64.zero;
    i <- 0;
    while (i < 2) {
      m.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    if ((inlen \ult (W64.of_int 8))) {
      c <- (W64.of_int 0);
      n <- (W64.of_int 0);
      
      while ((c \ult inlen)) {
        t <- (zeroextu64 (loadW8 Glob.mem (in_0 + c)));
        t <- (t `<<` (truncateu8 n));
        m.[0] <- (m.[0] `|` t);
        n <- (n + (W64.of_int 8));
        c <- (c + (W64.of_int 1));
      }
      t <- (W64.of_int 1);
      t <- (t `<<` (truncateu8 n));
      m.[0] <- (m.[0] `|` t);
    } else {
      m.[0] <- (loadW64 Glob.mem (in_0 + (W64.of_int 0)));
      inlen <- (inlen - (W64.of_int 8));
      in_0 <- (in_0 + (W64.of_int 8));
      c <- (W64.of_int 0);
      n <- (W64.of_int 0);
      
      while ((c \ult inlen)) {
        t <- (zeroextu64 (loadW8 Glob.mem (in_0 + c)));
        t <- (t `<<` (truncateu8 n));
        m.[1] <- (m.[1] `|` t);
        n <- (n + (W64.of_int 8));
        c <- (c + (W64.of_int 1));
      }
      t <- (W64.of_int 1);
      t <- (t `<<` (truncateu8 n));
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
  
  proc pack (y:W64.t, x:W64.t Array5.t) : unit = {
    
    var t:W64.t;
    var t1:W64.t;
    
    t <- x.[0];
    t1 <- x.[1];
    t1 <- (t1 `<<` (W8.of_int 26));
    t <- (t `|` t1);
    t1 <- x.[2];
    t1 <- (t1 `<<` (W8.of_int 52));
    t <- (t `|` t1);
    Glob.mem <- storeW64 Glob.mem (y + (W64.of_int (0 * 8))) t;
    t <- x.[2];
    t <- (t `&` (W64.of_int 67108863));
    t <- (t `>>` (W8.of_int 12));
    t1 <- x.[3];
    t1 <- (t1 `<<` (W8.of_int 14));
    t <- (t `|` t1);
    t1 <- x.[4];
    t1 <- (t1 `<<` (W8.of_int 40));
    t <- (t `|` t1);
    Glob.mem <- storeW64 Glob.mem (y + (W64.of_int (1 * 8))) t;
    return ();
  }
  
  proc load_4x (in_0:W64.t) : W64.t Array5.t * W64.t Array5.t *
                              W64.t Array5.t * W64.t Array5.t * W64.t = {
    
    var x0:W64.t Array5.t;
    var x1:W64.t Array5.t;
    var x2:W64.t Array5.t;
    var x3:W64.t Array5.t;
    x0 <- Array5.create W64.zero;
    x1 <- Array5.create W64.zero;
    x2 <- Array5.create W64.zero;
    x3 <- Array5.create W64.zero;
    x0 <@ load (in_0);
    in_0 <- (in_0 + (W64.of_int 16));
    x1 <@ load (in_0);
    in_0 <- (in_0 + (W64.of_int 16));
    x2 <@ load (in_0);
    in_0 <- (in_0 + (W64.of_int 16));
    x3 <@ load (in_0);
    in_0 <- (in_0 + (W64.of_int 16));
    return (x0, x1, x2, x3, in_0);
  }
  
  proc add_4x (h0:W64.t Array5.t, h1:W64.t Array5.t, h2:W64.t Array5.t,
               h3:W64.t Array5.t, x0:W64.t Array5.t, x1:W64.t Array5.t,
               x2:W64.t Array5.t, x3:W64.t Array5.t) : W64.t Array5.t *
                                                       W64.t Array5.t *
                                                       W64.t Array5.t *
                                                       W64.t Array5.t = {
    
    
    
    h0 <@ add (h0, x0);
    h1 <@ add (h1, x1);
    h2 <@ add (h2, x2);
    h3 <@ add (h3, x3);
    return (h0, h1, h2, h3);
  }
  
  proc mulmod_4x (h0:W64.t Array5.t, h1:W64.t Array5.t, h2:W64.t Array5.t,
                  h3:W64.t Array5.t, r4:W64.t Array5.t, r3:W64.t Array5.t,
                  r2:W64.t Array5.t, r:W64.t Array5.t, r4x5:W64.t Array4.t,
                  r3x5:W64.t Array4.t, r2x5:W64.t Array4.t,
                  rx5:W64.t Array4.t) : W64.t Array5.t * W64.t Array5.t *
                                        W64.t Array5.t * W64.t Array5.t = {
    
    
    
    h0 <@ mulmod (h0, r4, r4x5);
    h1 <@ mulmod (h1, r3, r3x5);
    h2 <@ mulmod (h2, r2, r2x5);
    h3 <@ mulmod (h3, r, rx5);
    return (h0, h1, h2, h3);
  }
  
  proc carry_reduce_4x (h0:W64.t Array5.t, h1:W64.t Array5.t,
                        h2:W64.t Array5.t, h3:W64.t Array5.t) : W64.t Array5.t *
                                                                W64.t Array5.t *
                                                                W64.t Array5.t *
                                                                W64.t Array5.t = {
    
    
    
    h0 <@ carry_reduce (h0);
    h1 <@ carry_reduce (h1);
    h2 <@ carry_reduce (h2);
    h3 <@ carry_reduce (h3);
    return (h0, h1, h2, h3);
  }
  
  proc add4 (h0:W64.t Array5.t, h1:W64.t Array5.t, h2:W64.t Array5.t,
             h3:W64.t Array5.t) : W64.t Array5.t = {
    
    var h:W64.t Array5.t;
    var ha:W64.t Array5.t;
    var hb:W64.t Array5.t;
    h <- Array5.create W64.zero;
    ha <- Array5.create W64.zero;
    hb <- Array5.create W64.zero;
    ha <@ add (h0, h1);
    hb <@ add (h2, h3);
    h <@ add (ha, hb);
    return (h);
  }
  
  proc poly1305 (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    var aux: int;
    
    var r:W64.t Array5.t;
    var i:int;
    var rx5:W64.t Array4.t;
    var h:W64.t Array5.t;
    var b64:W64.t;
    var r2:W64.t Array5.t;
    var r2x5:W64.t Array4.t;
    var r3:W64.t Array5.t;
    var r4:W64.t Array5.t;
    var r4x5:W64.t Array4.t;
    var r3x5:W64.t Array4.t;
    var x0:W64.t Array5.t;
    var x1:W64.t Array5.t;
    var x2:W64.t Array5.t;
    var x3:W64.t Array5.t;
    var h0:W64.t Array5.t;
    var h1:W64.t Array5.t;
    var h2:W64.t Array5.t;
    var h3:W64.t Array5.t;
    var b16:W64.t;
    var x:W64.t Array5.t;
    var s:W64.t Array5.t;
    h <- Array5.create W64.zero;
    h0 <- Array5.create W64.zero;
    h1 <- Array5.create W64.zero;
    h2 <- Array5.create W64.zero;
    h3 <- Array5.create W64.zero;
    r <- Array5.create W64.zero;
    r2 <- Array5.create W64.zero;
    r2x5 <- Array4.create W64.zero;
    r3 <- Array5.create W64.zero;
    r3x5 <- Array4.create W64.zero;
    r4 <- Array5.create W64.zero;
    r4x5 <- Array4.create W64.zero;
    rx5 <- Array4.create W64.zero;
    s <- Array5.create W64.zero;
    x <- Array5.create W64.zero;
    x0 <- Array5.create W64.zero;
    x1 <- Array5.create W64.zero;
    x2 <- Array5.create W64.zero;
    x3 <- Array5.create W64.zero;
    r <@ clamp (k);
    i <- 0;
    while (i < 4) {
      rx5.[i] <- (r.[(i + 1)] * (W64.of_int 5));
      i <- i + 1;
    }
    i <- 0;
    while (i < 5) {
      h.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    b64 <- inlen;
    b64 <- (b64 `>>` (W8.of_int 6));
    if (((W64.of_int 1) \ult b64)) {
      inlen <- (inlen `&` (W64.of_int 63));
      b64 <- (b64 - (W64.of_int 2));
      r2 <- r;
      r2 <@ mulmod (r2, r, rx5);
      r2 <@ carry_reduce (r2);
      i <- 0;
      while (i < 4) {
        r2x5.[i] <- (r2.[(i + 1)] * (W64.of_int 5));
        i <- i + 1;
      }
      r3 <- r2;
      r3 <@ mulmod (r3, r, rx5);
      r3 <@ carry_reduce (r3);
      r4 <- r2;
      r4 <@ mulmod (r4, r2, r2x5);
      r4 <@ carry_reduce (r4);
      i <- 0;
      while (i < 4) {
        r4x5.[i] <- (r4.[(i + 1)] * (W64.of_int 5));
        i <- i + 1;
      }
      i <- 0;
      while (i < 4) {
        r3x5.[i] <- (r3.[(i + 1)] * (W64.of_int 5));
        i <- i + 1;
      }
      (x0, x1, x2, x3, in_0) <@ load_4x (in_0);
      (h0, h1, h2, h3) <@ mulmod_4x (x0, x1, x2, x3, r4, r4, r4, r4, r4x5,
      r4x5, r4x5, r4x5);
      (h0, h1, h2, h3) <@ carry_reduce_4x (h0, h1, h2, h3);
      
      while (((W64.of_int 0) \ult b64)) {
        (x0, x1, x2, x3, in_0) <@ load_4x (in_0);
        (h0, h1, h2, h3) <@ add_4x (h0, h1, h2, h3, x0, x1, x2, x3);
        (h0, h1, h2, h3) <@ mulmod_4x (h0, h1, h2, h3, r4, r4, r4, r4, r4x5,
        r4x5, r4x5, r4x5);
        (h0, h1, h2, h3) <@ carry_reduce_4x (h0, h1, h2, h3);
        b64 <- (b64 - (W64.of_int 1));
      }
      (x0, x1, x2, x3, in_0) <@ load_4x (in_0);
      (h0, h1, h2, h3) <@ add_4x (h0, h1, h2, h3, x0, x1, x2, x3);
      (h0, h1, h2, h3) <@ mulmod_4x (h0, h1, h2, h3, r4, r3, r2, r, r4x5,
      r3x5, r2x5, rx5);
      (h0, h1, h2, h3) <@ carry_reduce_4x (h0, h1, h2, h3);
      h <@ add4 (h0, h1, h2, h3);
      h <@ carry_reduce (h);
    } else {
      
    }
    b16 <- inlen;
    b16 <- (b16 `>>` (W8.of_int 4));
    
    while (((W64.of_int 0) \ult b16)) {
      b16 <- (b16 - (W64.of_int 1));
      x <@ load (in_0);
      in_0 <- (in_0 + (W64.of_int 16));
      h <@ add (h, x);
      h <@ mulmod (h, r, rx5);
      h <@ carry_reduce (h);
    }
    inlen <- (inlen `&` (W64.of_int 15));
    if ((inlen <> (W64.of_int 0))) {
      x <@ load_last (in_0, inlen);
      h <@ add (h, x);
      h <@ mulmod (h, r, rx5);
      h <@ carry_reduce (h);
    } else {
      
    }
    h <@ freeze (h);
    k <- (k + (W64.of_int 16));
    s <@ unpack (k);
    h <@ add_carry (h, s);
    pack (out, h);
    return ();
  }
}.

