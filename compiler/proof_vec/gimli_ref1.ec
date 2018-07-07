require import Jasmin_model Int IntDiv CoreMap.



module M = {
  proc rotate (x:W32.t, bits:int) : W32.t = {
    
    
    x <- ((x `<<` (W8.of_uint bits)) `^` (x `>>` (W8.of_uint (32 - bits))));
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
        x <@ rotate (x, 24);
        y <- state.[(4 + column)];
        y <@ rotate (y, 9);
        z <- state.[(8 + column)];
        state.[(8 + column)] <- ((x `^` (z `<<` (W8.of_uint 1))) `^` ((y `&` z) `<<` (W8.of_uint 2)));
        state.[(4 + column)] <- ((y `^` x) `^` ((x `|` z) `<<` (W8.of_uint 1)));
        state.[column] <- ((z `^` y) `^` ((x `&` y) `<<` (W8.of_uint 3)));
        column <- column + 1;
      }
      if (((round %% 4) = 0)) {
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
      if (((round %% 4) = 2)) {
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
      if (((round %% 4) = 0)) {
        state.[0] <- (state.[0] `^` ((W32.of_uint 2654435584) `^` (W32.of_uint round)));
      } else {
        
      }
      round <- round - 1;
    }
    return (state);
  }
}.

