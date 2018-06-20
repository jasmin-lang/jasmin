require import Jasmin_model Int IntDiv CoreMap.



module M = {
  proc add (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    
    x.[0] <- (x.[0] + y.[0]);
    x.[1] <- (x.[1] + y.[1]);
    x.[2] <- (x.[2] + y.[2]);
    return (x);
  }
  
  proc add_stack (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    
    x.[0] <- (x.[0] + y.[0]);
    x.[1] <- (x.[1] + y.[1]);
    x.[2] <- (x.[2] + y.[2]);
    return (x);
  }
  
  proc add_carry (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    var t:W64.t;
    x.[0] <- (x.[0] + y.[0]);
    t <- x.[0];
    t <- (t `>>` (W8.of_int 52));
    x.[1] <- (x.[1] + y.[1]);
    x.[1] <- (x.[1] + t);
    t <- x.[1];
    t <- (t `>>` (W8.of_int 52));
    x.[2] <- (x.[2] + y.[2]);
    x.[2] <- (x.[2] + t);
    x.[0] <- (x.[0] `&` (W64.of_int 4503599627370495));
    x.[1] <- (x.[1] `&` (W64.of_int 4503599627370495));
    return (x);
  }
  
  proc freeze (x:(int,W64.t)map) : (int,W64.t)map = {
    var i:int;
    var ox:(int,W64.t)map;
    var mp:(int,W64.t)map;
    var n:W64.t;
    i <- 0;
    while (i < 3) {
     ox.[i] <- x.[i];
    i <- i + 1;
    }
    mp.[0] <- (W64.of_int 5);
    mp.[1] <- (W64.of_int 0);
    mp.[2] <- (W64.of_int 67108864);
    x <@ add_carry (x, mp);
    n <- x.[2];
    n <- (n `>>` (W8.of_int 26));
    n <- (n `&` (W64.of_int 1));
    n <- (- n);
    ox.[0] <- (ox.[0] `^` x.[0]);
    ox.[1] <- (ox.[1] `^` x.[1]);
    ox.[2] <- (ox.[2] `^` x.[2]);
    ox.[0] <- (ox.[0] `&` n);
    ox.[1] <- (ox.[1] `&` n);
    ox.[2] <- (ox.[2] `&` n);
    x.[0] <- (x.[0] `^` ox.[0]);
    x.[1] <- (x.[1] `^` ox.[1]);
    x.[2] <- (x.[2] `^` ox.[2]);
    return (x);
  }
  
  proc mulmod (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    var t:W64.t;
    var h:W64.t;
    var l:W64.t;
    var th:W64.t;
    var tl:W64.t;
    var cf:bool;
    var xs:(int,W64.t)map;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    var  _20:bool;
    var  _21:bool;
    var  _22:bool;
    var  _23:bool;
    var  _24:bool;
    var  _25:bool;
    var  _26:bool;
    var  _27:bool;
    var  _28:bool;
    var  _29:bool;
    var  _30:bool;
    var  _31:bool;
    var  _32:bool;
    var  _33:bool;
    var  _34:bool;
    var  _35:bool;
    var  _36:bool;
    var  _37:bool;
    var  _38:bool;
    var  _39:bool;
    var  _40:bool;
    var  _41:bool;
    var  _42:bool;
    var  _43:bool;
    var  _44:bool;
    var  _45:bool;
    var  _46:bool;
    var  _47:bool;
    var  _48:bool;
    var  _49:bool;
    t <- (y.[2] * (W64.of_int 5));
    (h, l) <- mulu_64 t x.[1];
    ( _0,  _1,  _2,  _3,  _4, h) <- x86_SHLD_64 h l (W8.of_int 26);
    l <- (l `<<` (W8.of_int 26));
    th <- h;
    tl <- l;
    t <- x.[0];
    (h, l) <- mulu_64 t y.[0];
    (cf, tl) <- addc_64 tl l false;
    ( _5, th) <- addc_64 th h cf;
    t <- (y.[1] * (W64.of_int 5));
    (h, l) <- mulu_64 t x.[2];
    ( _6,  _7,  _8,  _9,  _10, h) <- x86_SHLD_64 h l (W8.of_int 26);
    l <- (l `<<` (W8.of_int 26));
    (cf, tl) <- addc_64 tl l false;
    ( _11, th) <- addc_64 th h cf;
    xs.[0] <- tl;
    xs.[0] <- (xs.[0] `&` (W64.of_int 4503599627370495));
    ( _12,  _13,  _14,  _15,  _16, tl) <- x86_SHRD_64 tl th (W8.of_int 52);
    th <- (th `>>` (W8.of_int 52));
    t <- x.[0];
    (h, l) <- mulu_64 t y.[1];
    (cf, tl) <- addc_64 tl l false;
    ( _17, th) <- addc_64 th h cf;
    t <- x.[1];
    (h, l) <- mulu_64 t y.[0];
    (cf, tl) <- addc_64 tl l false;
    ( _18, th) <- addc_64 th h cf;
    t <- (y.[2] * (W64.of_int 5));
    (h, l) <- mulu_64 t x.[2];
    ( _19,  _20,  _21,  _22,  _23, h) <- x86_SHLD_64 h l (W8.of_int 26);
    l <- (l `<<` (W8.of_int 26));
    (cf, tl) <- addc_64 tl l false;
    ( _24, th) <- addc_64 th h cf;
    xs.[1] <- tl;
    xs.[1] <- (xs.[1] `&` (W64.of_int 4503599627370495));
    ( _25,  _26,  _27,  _28,  _29, tl) <- x86_SHRD_64 tl th (W8.of_int 52);
    th <- (th `>>` (W8.of_int 52));
    t <- x.[0];
    (h, l) <- mulu_64 t y.[2];
    (cf, tl) <- addc_64 tl l false;
    ( _30, th) <- addc_64 th h cf;
    t <- x.[1];
    (h, l) <- mulu_64 t y.[1];
    (cf, tl) <- addc_64 tl l false;
    ( _31, th) <- addc_64 th h cf;
    t <- x.[2];
    (h, l) <- mulu_64 t y.[0];
    (cf, tl) <- addc_64 tl l false;
    ( _32, th) <- addc_64 th h cf;
    xs.[2] <- tl;
    xs.[2] <- (xs.[2] `&` (W64.of_int 67108863));
    ( _33,  _34,  _35,  _36,  _37, tl) <- x86_SHRD_64 tl th (W8.of_int 26);
    th <- (th `>>` (W8.of_int 26));
    t <- tl;
    (h, tl) <- mulu_64 t (W64.of_int 5);
    th <- (th * (W64.of_int 5));
    (cf, tl) <- addc_64 tl xs.[0] false;
    ( _38, th) <- addc_64 th h cf;
    xs.[0] <- tl;
    xs.[0] <- (xs.[0] `&` (W64.of_int 4503599627370495));
    ( _39,  _40,  _41,  _42,  _43, tl) <- x86_SHRD_64 tl th (W8.of_int 52);
    th <- (th `>>` (W8.of_int 52));
    (cf, tl) <- addc_64 tl xs.[1] false;
    ( _44, th) <- addc_64 th (W64.of_int 0) cf;
    xs.[1] <- tl;
    xs.[1] <- (xs.[1] `&` (W64.of_int 4503599627370495));
    ( _45,  _46,  _47,  _48,  _49, tl) <- x86_SHRD_64 tl th (W8.of_int 52);
    th <- (th `>>` (W8.of_int 52));
    (cf, tl) <- addc_64 tl xs.[2] false;
    xs.[2] <- tl;
    i <- 0;
    while (i < 3) {
     x.[i] <- xs.[i];
    i <- i + 1;
    }
    return (x);
  }
  
  proc unpack (global_mem : global_mem_t, y:W64.t) : global_mem_t * (int,W64.t)map = {
    var x:(int,W64.t)map;
    var t:W64.t;
    x.[0] <- (loadW64 global_mem (y + (W64.of_int (0 * 8))));
    x.[1] <- x.[0];
    x.[0] <- (x.[0] `&` (W64.of_int 4503599627370495));
    x.[1] <- (x.[1] `>>` (W8.of_int 52));
    x.[2] <- (loadW64 global_mem (y + (W64.of_int (1 * 8))));
    t <- x.[2];
    t <- (t `<<` (W8.of_int 12));
    x.[1] <- (x.[1] `|` t);
    x.[1] <- (x.[1] `&` (W64.of_int 4503599627370495));
    x.[2] <- (x.[2] `>>` (W8.of_int 40));
    return (global_mem, x);
  }
  
  proc pack (global_mem : global_mem_t, s:W64.t, h:(int,W64.t)map) : 
  global_mem_t = {
    var x:(int,W64.t)map;
    x.[0] <- h.[0];
    x.[0] <- (x.[0] `&` (W64.of_int 4503599627370495));
    x.[1] <- h.[1];
    x.[1] <- (x.[1] `<<` (W8.of_int 52));
    x.[0] <- (x.[0] `|` x.[1]);
    global_mem <- storeW64 global_mem (s + (W64.of_int 0)) x.[0];
    h.[1] <- (h.[1] `>>` (W8.of_int 12));
    h.[1] <- (h.[1] `&` (W64.of_int 1099511627775));
    h.[2] <- (h.[2] `<<` (W8.of_int 40));
    h.[2] <- (h.[2] `|` h.[1]);
    global_mem <- storeW64 global_mem (s + (W64.of_int 8)) h.[2];
    return global_mem;
  }
  
  proc poly1305 (global_mem : global_mem_t, o:W64.t, in:W64.t, b16:W64.t,
                                            in_l:W64.t, k:W64.t) : global_mem_t = {
    var s_o:W64.t;
    var s_in:W64.t;
    var s_b16:W64.t;
    var s_in_l:W64.t;
    var s_k:W64.t;
    var r:(int,W64.t)map;
    var i:int;
    var s_r:(int,W64.t)map;
    var b64:W64.t;
    var h:(int,W64.t)map;
    var s_b64:W64.t;
    var i_0:int;
    var r2:(int,W64.t)map;
    var i_1:int;
    var r4:(int,W64.t)map;
    var i_2:int;
    var s_r2:(int,W64.t)map;
    var i_3:int;
    var s_r4:(int,W64.t)map;
    var x0:(int,W64.t)map;
    var i_4:int;
    var s_x0:(int,W64.t)map;
    var y0:(int,W64.t)map;
    var x1:(int,W64.t)map;
    var y1:(int,W64.t)map;
    var hx:(int,W64.t)map;
    var hy:(int,W64.t)map;
    var i_5:int;
    var s_hy:(int,W64.t)map;
    var i_6:int;
    var s_hx:(int,W64.t)map;
    var i_7:int;
    var i_8:int;
    var i_9:int;
    var p:(int,W64.t)map;
    s_o <- o;
    s_in <- in;
    s_b16 <- b16;
    s_in_l <- in_l;
    s_k <- k;
    (global_mem, r) <@ unpack (global_mem, k);
    r.[0] <- (r.[0] `&` (W64.of_int 4503582715936767));
    r.[1] <- (r.[1] `&` (W64.of_int 4434330394804479));
    r.[2] <- (r.[2] `&` (W64.of_int 1048575));
    i <- 0;
    while (i < 3) {
     s_r.[i] <- r.[i];
    i <- i + 1;
    }
    b64 <- b16;
    b64 <- (b64 `>>` (W8.of_int 2));
    h.[0] <- (W64.of_int 0);
    h.[1] <- (W64.of_int 0);
    h.[2] <- (W64.of_int 0);
    if (((W64.of_int 0) `<` b64)) {
      s_b64 <- b64;
      i_0 <- 0;
      while (i_0 < 3) {
       r2.[i_0] <- r.[i_0];
      i_0 <- i_0 + 1;
      }
      r2 <@ mulmod (r2, r);
      i_1 <- 0;
      while (i_1 < 3) {
       r4.[i_1] <- r2.[i_1];
      i_1 <- i_1 + 1;
      }
      r4 <@ mulmod (r4, r2);
      i_2 <- 0;
      while (i_2 < 3) {
       s_r2.[i_2] <- r2.[i_2];
      i_2 <- i_2 + 1;
      }
      i_3 <- 0;
      while (i_3 < 3) {
       s_r4.[i_3] <- r4.[i_3];
      i_3 <- i_3 + 1;
      }
      in <- s_in;
      (global_mem, x0) <@ unpack (global_mem, in);
      x0.[2] <- (x0.[2] `|` (W64.of_int 16777216));
      x0 <@ mulmod (x0, r2);
      i_4 <- 0;
      while (i_4 < 3) {
       s_x0.[i_4] <- x0.[i_4];
      i_4 <- i_4 + 1;
      }
      in <- s_in;
      in <- (in + (W64.of_int 16));
      (global_mem, y0) <@ unpack (global_mem, in);
      y0.[2] <- (y0.[2] `|` (W64.of_int 16777216));
      y0 <@ mulmod (y0, r2);
      in <- s_in;
      in <- (in + (W64.of_int 32));
      (global_mem, x1) <@ unpack (global_mem, in);
      x1.[2] <- (x1.[2] `|` (W64.of_int 16777216));
      in <- (in + (W64.of_int 16));
      (global_mem, y1) <@ unpack (global_mem, in);
      y1.[2] <- (y1.[2] `|` (W64.of_int 16777216));
      in <- (in + (W64.of_int 16));
      s_in <- in;
      hx <@ add (x0, x1);
      hy <@ add (y0, y1);
      i_5 <- 0;
      while (i_5 < 3) {
       s_hy.[i_5] <- hy.[i_5];
      i_5 <- i_5 + 1;
      }
      b64 <- s_b64;
      b64 <- (b64 - (W64.of_int 1));
      
      while (((W64.of_int 0) `<` b64)) {
        b64 <- (b64 - (W64.of_int 1));
        s_b64 <- b64;
        r4.[0] <- s_r4.[0];
        r4.[1] <- s_r4.[1];
        r4.[2] <- s_r4.[2];
        hx <@ mulmod (hx, r4);
        hy.[0] <- s_hy.[0];
        hy.[1] <- s_hy.[1];
        hy.[2] <- s_hy.[2];
        i_6 <- 0;
        while (i_6 < 3) {
         s_hx.[i_6] <- hx.[i_6];
        i_6 <- i_6 + 1;
        }
        hy <@ mulmod (hy, r4);
        i_7 <- 0;
        while (i_7 < 3) {
         s_hy.[i_7] <- hy.[i_7];
        i_7 <- i_7 + 1;
        }
        in <- s_in;
        (global_mem, x0) <@ unpack (global_mem, in);
        x0.[2] <- (x0.[2] `|` (W64.of_int 16777216));
        r2.[0] <- s_r2.[0];
        r2.[1] <- s_r2.[1];
        r2.[2] <- s_r2.[2];
        x0 <@ mulmod (x0, r2);
        i_8 <- 0;
        while (i_8 < 3) {
         s_x0.[i_8] <- x0.[i_8];
        i_8 <- i_8 + 1;
        }
        in <- s_in;
        in <- (in + (W64.of_int 16));
        (global_mem, y0) <@ unpack (global_mem, in);
        y0.[2] <- (y0.[2] `|` (W64.of_int 16777216));
        y0 <@ mulmod (y0, r2);
        hx.[0] <- s_hx.[0];
        hx.[1] <- s_hx.[1];
        hx.[2] <- s_hx.[2];
        hy <@ add_stack (y0, s_hy);
        hx <@ add_stack (hx, s_x0);
        in <- s_in;
        in <- (in + (W64.of_int 32));
        (global_mem, x1) <@ unpack (global_mem, in);
        in <- (in + (W64.of_int 16));
        x1.[2] <- (x1.[2] `|` (W64.of_int 16777216));
        hx <@ add (hx, x1);
        (global_mem, y1) <@ unpack (global_mem, in);
        in <- (in + (W64.of_int 16));
        s_in <- in;
        y1.[2] <- (y1.[2] `|` (W64.of_int 16777216));
        hy <@ add (hy, y1);
        i_9 <- 0;
        while (i_9 < 3) {
         s_hy.[i_9] <- hy.[i_9];
        i_9 <- i_9 + 1;
        }
        b64 <- s_b64;
      }
      r2.[0] <- s_r2.[0];
      r2.[1] <- s_r2.[1];
      r2.[2] <- s_r2.[2];
      hx <@ mulmod (hx, r2);
      r.[0] <- s_r.[0];
      r.[1] <- s_r.[1];
      r.[2] <- s_r.[2];
      hy <@ mulmod (hy, r);
      h <@ add_carry (hx, hy);
    } else {
      
    }
    b16 <- s_b16;
    b16 <- (b16 `&` (W64.of_int 3));
    r.[0] <- s_r.[0];
    r.[1] <- s_r.[1];
    r.[2] <- s_r.[2];
    
    while (((W64.of_int 0) `<` b16)) {
      b16 <- (b16 - (W64.of_int 1));
      s_b16 <- b16;
      in <- s_in;
      (global_mem, x0) <@ unpack (global_mem, in);
      x0.[2] <- (x0.[2] `|` (W64.of_int 16777216));
      in <- (in + (W64.of_int 16));
      s_in <- in;
      h <@ add (h, x0);
      h <@ mulmod (h, r);
      b16 <- s_b16;
    }
    in_l <- s_in_l;
    if ((in_l <> (W64.of_int 0))) {
      in <- s_in;
      (global_mem, x0) <@ unpack (global_mem, in_l);
      h <@ add (h, x0);
      h <@ mulmod (h, r);
    } else {
      
    }
    h <@ freeze (h);
    k <- s_k;
    k <- (k + (W64.of_int 16));
    (global_mem, p) <@ unpack (global_mem, k);
    h <@ add_carry (h, p);
    o <- s_o;
    global_mem <@ pack (global_mem, o, h);
    return global_mem;
  }
}.

