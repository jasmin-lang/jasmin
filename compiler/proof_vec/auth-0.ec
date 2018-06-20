require import Jasmin_model Int IntDiv CoreMap.



module M = {
  proc add (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    
    x.[0] <- (x.[0] + y.[0]);
    x.[1] <- (x.[1] + y.[1]);
    x.[2] <- (x.[2] + y.[2]);
    x.[3] <- (x.[3] + y.[3]);
    x.[4] <- (x.[4] + y.[4]);
    return (x);
  }
  
  proc add_carry (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    var t:W64.t;
    x.[0] <- (x.[0] + y.[0]);
    t <- x.[0];
    t <- (t `>>` (W8.of_int 26));
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    x.[1] <- (x.[1] + y.[1]);
    x.[1] <- (x.[1] + t);
    t <- x.[1];
    t <- (t `>>` (W8.of_int 26));
    x.[1] <- (x.[1] `&` (W64.of_int 67108863));
    x.[2] <- (x.[2] + y.[2]);
    x.[2] <- (x.[2] + t);
    t <- x.[2];
    t <- (t `>>` (W8.of_int 26));
    x.[2] <- (x.[2] `&` (W64.of_int 67108863));
    x.[3] <- (x.[3] + y.[3]);
    x.[3] <- (x.[3] + t);
    t <- x.[3];
    t <- (t `>>` (W8.of_int 26));
    x.[3] <- (x.[3] `&` (W64.of_int 67108863));
    x.[4] <- (x.[4] + y.[4]);
    x.[4] <- (x.[4] + t);
    return (x);
  }
  
  proc freeze (x:(int,W64.t)map) : (int,W64.t)map = {
    var i:int;
    var ox:(int,W64.t)map;
    var mp:(int,W64.t)map;
    var n:W64.t;
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
  
  proc mulmod (x:(int,W64.t)map, y:(int,W64.t)map) : (int,W64.t)map = {
    var t0:W64.t;
    var r:W64.t;
    var c:W64.t;
    var ts:(int,W64.t)map;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var t4:W64.t;
    t0 <- x.[1];
    t0 <- (t0 * y.[4]);
    r <- x.[2];
    r <- (r * y.[3]);
    t0 <- (t0 + r);
    r <- x.[3];
    r <- (r * y.[2]);
    t0 <- (t0 + r);
    r <- x.[4];
    r <- (r * y.[1]);
    t0 <- (t0 + r);
    t0 <- (t0 * (W64.of_int 5));
    r <- x.[0];
    r <- (r * y.[0]);
    t0 <- (t0 + r);
    c <- t0;
    t0 <- (t0 `&` (W64.of_int 67108863));
    ts.[0] <- t0;
    c <- (c `>>` (W8.of_int 26));
    t1 <- x.[2];
    t1 <- (t1 * y.[4]);
    r <- x.[3];
    r <- (r * y.[3]);
    t1 <- (t1 + r);
    r <- x.[4];
    r <- (r * y.[2]);
    t1 <- (t1 + r);
    t1 <- (t1 * (W64.of_int 5));
    r <- x.[0];
    r <- (r * y.[1]);
    t1 <- (t1 + r);
    r <- x.[1];
    r <- (r * y.[0]);
    t1 <- (t1 + r);
    t1 <- (t1 + c);
    c <- t1;
    t1 <- (t1 `&` (W64.of_int 67108863));
    ts.[1] <- t1;
    c <- (c `>>` (W8.of_int 26));
    t2 <- x.[3];
    t2 <- (t2 * y.[4]);
    r <- x.[4];
    r <- (r * y.[3]);
    t2 <- (t2 + r);
    t2 <- (t2 * (W64.of_int 5));
    r <- x.[0];
    r <- (r * y.[2]);
    t2 <- (t2 + r);
    r <- x.[1];
    r <- (r * y.[1]);
    t2 <- (t2 + r);
    r <- x.[2];
    r <- (r * y.[0]);
    t2 <- (t2 + r);
    t2 <- (t2 + c);
    c <- t2;
    t2 <- (t2 `&` (W64.of_int 67108863));
    ts.[2] <- t2;
    c <- (c `>>` (W8.of_int 26));
    t3 <- x.[4];
    t3 <- (t3 * y.[4]);
    t3 <- (t3 * (W64.of_int 5));
    r <- x.[0];
    r <- (r * y.[3]);
    t3 <- (t3 + r);
    r <- x.[1];
    r <- (r * y.[2]);
    t3 <- (t3 + r);
    r <- x.[2];
    r <- (r * y.[1]);
    t3 <- (t3 + r);
    r <- x.[3];
    r <- (r * y.[0]);
    t3 <- (t3 + r);
    t3 <- (t3 + c);
    c <- t3;
    t3 <- (t3 `&` (W64.of_int 67108863));
    ts.[3] <- t3;
    c <- (c `>>` (W8.of_int 26));
    t4 <- x.[0];
    t4 <- (t4 * y.[4]);
    r <- x.[1];
    r <- (r * y.[3]);
    t4 <- (t4 + r);
    r <- x.[2];
    r <- (r * y.[2]);
    t4 <- (t4 + r);
    r <- x.[3];
    r <- (r * y.[1]);
    t4 <- (t4 + r);
    r <- x.[4];
    r <- (r * y.[0]);
    t4 <- (t4 + r);
    t4 <- (t4 + c);
    c <- t4;
    t4 <- (t4 `&` (W64.of_int 67108863));
    ts.[4] <- t4;
    c <- (c `>>` (W8.of_int 26));
    c <- (c * (W64.of_int 5));
    x.[0] <- ts.[0];
    x.[1] <- ts.[1];
    x.[2] <- ts.[2];
    x.[3] <- ts.[3];
    x.[4] <- ts.[4];
    x.[0] <- (x.[0] + c);
    c <- x.[0];
    c <- (c `>>` (W8.of_int 26));
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    x.[1] <- (x.[1] + c);
    c <- x.[1];
    c <- (c `>>` (W8.of_int 26));
    x.[1] <- (x.[1] `&` (W64.of_int 67108863));
    x.[2] <- (x.[2] + c);
    c <- x.[2];
    c <- (c `>>` (W8.of_int 26));
    x.[2] <- (x.[2] `&` (W64.of_int 67108863));
    x.[3] <- (x.[3] + c);
    c <- x.[3];
    c <- (c `>>` (W8.of_int 26));
    x.[3] <- (x.[3] `&` (W64.of_int 67108863));
    x.[4] <- (x.[4] + c);
    return (x);
  }
  
  proc unpack (global_mem : global_mem_t, y:W64.t) : global_mem_t * (int,W64.t)map = {
    var x:(int,W64.t)map;
    var t:W64.t;
    x.[0] <- (loadW64 global_mem (y + (W64.of_int (0 * 8))));
    t <- x.[0];
    x.[0] <- (x.[0] `&` (W64.of_int 67108863));
    t <- (t `>>` (W8.of_int 26));
    x.[1] <- t;
    x.[1] <- (x.[1] `&` (W64.of_int 67108863));
    t <- (t `>>` (W8.of_int 26));
    x.[2] <- t;
    x.[3] <- (loadW64 global_mem (y + (W64.of_int (1 * 8))));
    t <- x.[3];
    t <- (t `<<` (W8.of_int 12));
    x.[2] <- (x.[2] `|` t);
    x.[2] <- (x.[2] `&` (W64.of_int 67108863));
    x.[4] <- x.[3];
    x.[3] <- (x.[3] `>>` (W8.of_int 14));
    x.[4] <- (x.[4] `>>` (W8.of_int 40));
    x.[3] <- (x.[3] `&` (W64.of_int 67108863));
    x.[4] <- (x.[4] `&` (W64.of_int 67108863));
    return (global_mem, x);
  }
  
  proc pack (global_mem : global_mem_t, y:W64.t, x:(int,W64.t)map) : 
  global_mem_t = {
    var t:W64.t;
    var t1:W64.t;
    t <- x.[0];
    t <- (t `&` (W64.of_int 67108863));
    t1 <- x.[1];
    t1 <- (t1 `&` (W64.of_int 67108863));
    t1 <- (t1 `<<` (W8.of_int 26));
    t <- (t `|` t1);
    t1 <- x.[2];
    t1 <- (t1 `&` (W64.of_int 67108863));
    t1 <- (t1 `<<` (W8.of_int 52));
    t <- (t `|` t1);
    global_mem <- storeW64 global_mem (y + (W64.of_int (0 * 8))) t;
    t <- x.[2];
    t <- (t `&` (W64.of_int 67108863));
    t <- (t `>>` (W8.of_int 12));
    t1 <- x.[3];
    t1 <- (t1 `&` (W64.of_int 67108863));
    t1 <- (t1 `<<` (W8.of_int 14));
    t <- (t `|` t1);
    t1 <- x.[4];
    t1 <- (t1 `&` (W64.of_int 67108863));
    t1 <- (t1 `<<` (W8.of_int 40));
    t <- (t `|` t1);
    global_mem <- storeW64 global_mem (y + (W64.of_int (1 * 8))) t;
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
    var i_0:int;
    var rs:(int,W64.t)map;
    var h:(int,W64.t)map;
    var c:(int,W64.t)map;
    os <- o;
    ibs <- ib;
    iblens <- iblen;
    is <- i;
    ks <- k;
    (global_mem, r) <@ unpack (global_mem, k);
    r.[0] <- (r.[0] `&` (W64.of_int 67108863));
    r.[1] <- (r.[1] `&` (W64.of_int 67108611));
    r.[2] <- (r.[2] `&` (W64.of_int 67092735));
    r.[3] <- (r.[3] `&` (W64.of_int 66076671));
    r.[4] <- (r.[4] `&` (W64.of_int 1048575));
    i_0 <- 0;
    while (i_0 < 5) {
     rs.[i_0] <- r.[i_0];
    i_0 <- i_0 + 1;
    }
    h.[0] <- (W64.of_int 0);
    h.[1] <- (W64.of_int 0);
    h.[2] <- (W64.of_int 0);
    h.[3] <- (W64.of_int 0);
    h.[4] <- (W64.of_int 0);
    
    while (((W64.of_int 0) `<` iblen)) {
      iblen <- (iblen - (W64.of_int 1));
      iblens <- iblen;
      ib <- ibs;
      (global_mem, c) <@ unpack (global_mem, ib);
      ib <- (ib + (W64.of_int 16));
      ibs <- ib;
      c.[4] <- (c.[4] `|` (W64.of_int 16777216));
      h <@ add (h, c);
      h <@ mulmod (h, rs);
      iblen <- iblens;
    }
    i <- is;
    if ((i <> (W64.of_int 0))) {
      (global_mem, c) <@ unpack (global_mem, i);
      h <@ add (h, c);
      h <@ mulmod (h, rs);
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

