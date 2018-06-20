require import Jasmin_model Int IntDiv CoreMap.



module M = {
  proc rotate (x:W32.t, bits:int) : W32.t = {
    var  _0:bool;
    var  _1:bool;
    ( _0,  _1, x) <- x86_ROL_32 x (W8.of_int bits);
    return (x);
  }
  
  proc gimli (global_mem : global_mem_t, state:W64.t) : global_mem_t = {
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var round:int;
    round <- 0;
    while (24 < round) {
     column <- 0;
     while (column < 4) {
      x <- (loadW32 global_mem (state + (W64.of_int (4 * column))));
      x <@ rotate (x, 24);
      y <- (loadW32 global_mem (state + (W64.of_int (4 * (4 + column)))));
      y <@ rotate (y, 9);
      z <- (loadW32 global_mem (state + (W64.of_int (4 * (8 + column)))));
      a <- x;
      b <- z;
      b <- (b `<<` (W8.of_int 1));
      c <- y;
      c <- (c `&` z);
      c <- (c `<<` (W8.of_int 2));
      a <- (a `^` b);
      a <- (a `^` c);
      global_mem <- storeW32 global_mem (state + (W64.of_int (4 * (8 + column)))) a;
      a <- y;
      b <- x;
      b <- (b `|` z);
      b <- (b `<<` (W8.of_int 1));
      a <- (a `^` x);
      a <- (a `^` b);
      global_mem <- storeW32 global_mem (state + (W64.of_int (4 * (4 + column)))) a;
      a <- z;
      b <- x;
      b <- (b `&` y);
      b <- (b `<<` (W8.of_int 3));
      a <- (a `^` y);
      a <- (a `^` b);
      global_mem <- storeW32 global_mem (state + (W64.of_int (4 * column))) a;
     column <- column + 1;
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 0))) {
       x <- (loadW32 global_mem (state + (W64.of_int (4 * 0))));
       y <- (loadW32 global_mem (state + (W64.of_int (4 * 1))));
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 0))) y;
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 1))) x;
       x <- (loadW32 global_mem (state + (W64.of_int (4 * 2))));
       y <- (loadW32 global_mem (state + (W64.of_int (4 * 3))));
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 2))) y;
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 3))) x;
     } else {
       
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 2))) {
       x <- (loadW32 global_mem (state + (W64.of_int (4 * 0))));
       y <- (loadW32 global_mem (state + (W64.of_int (4 * 2))));
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 0))) y;
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 2))) x;
       x <- (loadW32 global_mem (state + (W64.of_int (4 * 1))));
       y <- (loadW32 global_mem (state + (W64.of_int (4 * 3))));
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 1))) y;
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 3))) x;
     } else {
       
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 0))) {
       global_mem <- storeW32 global_mem (state + (W64.of_int (4 * 0))) ((loadW32 global_mem (state + (W64.of_int (4 * 0)))) `^` (W32.of_int (2654435584 + round)));
     } else {
       
     }
    round <- round - 1;
    }
    return global_mem;
  }
}.

