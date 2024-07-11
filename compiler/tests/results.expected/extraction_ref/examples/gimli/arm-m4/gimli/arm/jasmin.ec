require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array12.
require import WArray48.



module M = {
  proc swap_0 (state:W32.t Array12.t, i:int, j:int) : W32.t Array12.t = {
    
    var x:W32.t;
    var y:W32.t;
    
    x <- state.[i];
    y <- state.[j];
    state.[i] <- y;
    state.[j] <- x;
    return (state);
  }
  
  proc gimli (state:W32.t Array12.t) : W32.t Array12.t = {
    var aux: int;
    
    var rc:W32.t;
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var a:W32.t;
    var b:W32.t;
    var round:int;
    
    rc <- (W32.of_int 2654435584);
    round <- 24;
    while (0 < round) {
      column <- 0;
      while (column < 4) {
        x <- state.[(0 + column)];
        x <- (x `|<<|` (W8.of_int 24));
        y <- state.[(4 + column)];
        y <- (y `|<<|` (W8.of_int 9));
        z <- state.[(8 + column)];
        a <- (x `^` (z `<<` (W8.of_int 1)));
        b <- (y `&` z);
        a <- (a `^` (b `<<` (W8.of_int 2)));
        state.[(8 + column)] <- a;
        a <- (y `^` x);
        b <- (x `|` z);
        a <- (a `^` (b `<<` (W8.of_int 1)));
        state.[(4 + column)] <- a;
        a <- (z `^` y);
        b <- (x `&` y);
        a <- (a `^` (b `<<` (W8.of_int 3)));
        state.[(0 + column)] <- a;
        column <- column + 1;
      }
      if (((round %% 4) = 0)) {
        state <@ swap_0 (state, 0, 1);
        state <@ swap_0 (state, 2, 3);
      } else {
        
      }
      if (((round %% 4) = 2)) {
        state <@ swap_0 (state, 0, 2);
        state <@ swap_0 (state, 1, 3);
      } else {
        
      }
      if (((round %% 4) = 0)) {
        a <- state.[0];
        b <- (rc + (W32.of_int round));
        a <- (a `^` b);
        state.[0] <- a;
      } else {
        
      }
      round <- round - 1;
    }
    return (state);
  }
}.

