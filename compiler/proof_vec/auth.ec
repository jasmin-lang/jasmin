require import Jasmin_model Int IntDiv CoreMap.



module M = {
  proc add (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    
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
  
  proc poly1305 (global_mem : global_mem_t, o:W64.t, ib:W64.t, iblen:W64.t,
                                            i:W64.t, k:W64.t) : global_mem_t = {
    var os:W64.t;
    var ibs:W64.t;
    var iblens:W64.t;
    var is:W64.t;
    var ks:W64.t;
    var r:(int,W64.t)map;
    var h:(int,W64.t)map;
    var c:(int,W64.t)map;
    os <- o;
    ibs <- ib;
    iblens <- iblen;
    is <- i;
    ks <- k;
    (global_mem, r) <@ unpack (global_mem, k);
    r.[0] <- (r.[0] `&` (W64.of_int 4503582715936767));
    r.[1] <- (r.[1] `&` (W64.of_int 4434330394804479));
    r.[2] <- (r.[2] `&` (W64.of_int 1048575));
    h.[0] <- (W64.of_int 0);
    h.[1] <- (W64.of_int 0);
    h.[2] <- (W64.of_int 0);
    
    while (((W64.of_int 0) `<` iblen)) {
      iblen <- (iblen - (W64.of_int 1));
      iblens <- iblen;
      ib <- ibs;
      (global_mem, c) <@ unpack (global_mem, ib);
      ib <- (ib + (W64.of_int 16));
      ibs <- ib;
      c.[2] <- (c.[2] `|` (W64.of_int 16777216));
      h <@ add (h, c);
      h <@ mulmod (h, r);
      iblen <- iblens;
    }
    i <- is;
    if ((i <> (W64.of_int 0))) {
      (global_mem, c) <@ unpack (global_mem, i);
      h <@ add (h, c);
      h <@ mulmod (h, r);
    } else {
      
    }
    h <@ freeze (h);
    k <- ks;
    k <- (k + (W64.of_int 16));
    (global_mem, c) <@ unpack (global_mem, k);
    h <@ add_carry (h, c);
    o <- os;
    global_mem <@ pack (global_mem, o, h);
    return global_mem;
  }
}.

