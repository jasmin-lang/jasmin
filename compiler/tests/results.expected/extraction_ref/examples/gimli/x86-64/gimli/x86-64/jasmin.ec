require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array12.
require import WArray48.



module M = {
  proc gimli (state:W32.t Array12.t) : W32.t Array12.t = {
    var aux: int;
    
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var round:int;
    
    round <- 24;
    while (0 < round) {
      column <- 0;
      while (column < 4) {
        x <- state.[(0 + column)];
        x <- (x `|<<|` (W8.of_int 24));
        y <- state.[(4 + column)];
        y <- (y `|<<|` (W8.of_int 9));
        z <- state.[(8 + column)];
        a <- x;
        b <- z;
        b <- (b `<<` (W8.of_int 1));
        c <- y;
        c <- (c `&` z);
        c <- (c `<<` (W8.of_int 2));
        a <- (a `^` b);
        a <- (a `^` c);
        state.[(8 + column)] <- a;
        a <- y;
        b <- x;
        b <- (b `|` z);
        b <- (b `<<` (W8.of_int 1));
        a <- (a `^` x);
        a <- (a `^` b);
        state.[(4 + column)] <- a;
        a <- z;
        b <- x;
        b <- (b `&` y);
        b <- (b `<<` (W8.of_int 3));
        a <- (a `^` y);
        a <- (a `^` b);
        state.[(0 + column)] <- a;
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
        state.[0] <- (state.[0] `^` (W32.of_int (2654435584 + round)));
      } else {
        
      }
      round <- round - 1;
    }
    return (state);
  }
}.

