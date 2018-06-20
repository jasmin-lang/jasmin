require import Jasmin_model Int IntDiv CoreMap.

op rotate24pattern = (W128.of_int 16028905388486802350658220295983399425).


module M = {
  proc shift (x:W128.t, count:int) : W128.t = {
    var r:W128.t;
    r <- x86_VPSLL_4u32 x (W8.of_int count);
    return (r);
  }
  
  proc rotate (r:W128.t, count:int) : W128.t = {
    var a:W128.t;
    var b:W128.t;
    if ((count <> 0)) {
      if ((count = 24)) {
        r <- x86_VPSHUFB_128 r rotate24pattern;
      } else {
        a <@ shift (r, count);
        count <- (32 - count);
        b <- x86_VPSRL_4u32 r (W8.of_int count);
        r <- (a `|` b);
      }
    } else {
      
    }
    return (r);
  }
  
  proc shuffle (a:int, b:int, c:int, d:int) : int = {
    var r:int;
    r <- ((((a * 64) + (b * 16)) + (c * 4)) + d);
    return (r);
  }
  
  proc gimli (global_mem : global_mem_t, state:W64.t) : global_mem_t = {
    var x:W128.t;
    var y:W128.t;
    var z:W128.t;
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W128.t;
    var e:W128.t;
    var pattern:int;
    var round:int;
    var m:W32.t;
    x <- (loadW128 global_mem (state + (W64.of_int (16 * 0))));
    y <- (loadW128 global_mem (state + (W64.of_int (16 * 1))));
    z <- (loadW128 global_mem (state + (W64.of_int (16 * 2))));
    round <- 0;
    while (24 < round) {
     x <@ rotate (x, 24);
     y <@ rotate (y, 9);
     z <@ rotate (z, 0);
     a <@ shift (z, 1);
     b <- (y `&` z);
     c <@ shift (b, 2);
     d <- (x `^` a);
     e <- (d `^` c);
     a <- (x `|` z);
     b <@ shift (a, 1);
     c <- (y `^` x);
     d <- (c `^` b);
     a <- (x `&` y);
     b <@ shift (a, 3);
     c <- (z `^` y);
     x <- (c `^` b);
     y <- d;
     z <- e;
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 0))) {
       pattern <@ shuffle (2, 3, 0, 1);
       x <- x86_VPSHUFD_128 x (W8.of_int pattern);
     } else {
       
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 2))) {
       pattern <@ shuffle (1, 0, 3, 2);
       x <- x86_VPSHUFD_128 x (W8.of_int pattern);
     } else {
       
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 0))) {
       m <- (W32.of_int (2654435584 + round));
       a <- x86_MOVD_32 m;
       x <- (x `^` a);
     } else {
       
     }
    round <- round - 1;
    }
    global_mem <- storeW128 global_mem (state + (W64.of_int (16 * 0))) x;
    global_mem <- storeW128 global_mem (state + (W64.of_int (16 * 1))) y;
    global_mem <- storeW128 global_mem (state + (W64.of_int (16 * 2))) z;
    return global_mem;
  }
}.

