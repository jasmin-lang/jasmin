

module M = {
  proc rotate (x:W32.t, bits:int) : W32.t = {
    
    (_, _, x) <- x86_ROL_32 x (W8.of_int bits);
    return (x);
  }
  
  proc gimli_body (state:(int,W32.t)map) : (int,W32.t)map = {
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var round:int;
    round <- 0;
    while (24 < round) {
     column <- 0;
     while (column < 4) {
      x <- state.[column];
      x < rotate (x, 24);
      y <- state.[(4 + column)];
      y < rotate (y, 9);
      z <- state.[(8 + column)];
      state.[(8 + column)] <- ((x `^` (z `<<` (W8.of_int 1))) `^` ((y `&` z) `<<` (W8.of_int 2)));
      state.[(4 + column)] <- ((y `^` x) `^` ((x `|` z) `<<` (W8.of_int 1)));
      state.[column] <- ((z `^` y) `^` ((x `&` y) `<<` (W8.of_int 3)));
     column <- column + 1;
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 0))) {
       x <- state.[0];
       y <- state.[1];
       state.[0] <- y;
       state.[1] <- x;
       x <- state.[2];
       y <- state.[3];
       state.[2] <- y;
       state.[3] <- x;
     } else {
       
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 2))) {
       x <- state.[0];
       y <- state.[2];
       state.[0] <- y;
       state.[2] <- x;
       x <- state.[1];
       y <- state.[3];
       state.[1] <- y;
       state.[3] <- x;
     } else {
       
     }
     if ((((W256.of_int round) `&` (W256.of_int 3)) = (W256.of_int 0))) {
       state.[0] <- (state.[0] `^` (W256.cast_32 ((W256.of_int 2654435584) `^` (W256.of_int round))));
     } else {
       
     }
    round <- round - 1;
    }
    return (state);
  }