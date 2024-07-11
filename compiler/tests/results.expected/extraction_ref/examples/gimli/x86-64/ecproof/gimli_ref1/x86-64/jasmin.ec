require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array12.
require import WArray48.



module M = {
  proc rotate (x:W32.t, bits:int) : W32.t = {
    
    
    
    x <- ((x `<<` (W8.of_int bits)) `^` (x `>>` (W8.of_int (32 - bits))));
    return (x);
  }
  
  proc gimli_body (state:W32.t Array12.t) : W32.t Array12.t = {
    var aux: int;
    
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var round:int;
    
    round <- 24;
    while (0 < round) {
      column <- 0;
      while (column < 4) {
        x <- state.[column];
        x <@ rotate (x, 24);
        y <- state.[(4 + column)];
        y <@ rotate (y, 9);
        z <- state.[(8 + column)];
        state.[(8 + column)] <- ((x `^` (z `<<` (W8.of_int 1))) `^` ((y `&` z) `<<` (W8.of_int 2)));
        state.[(4 + column)] <- ((y `^` x) `^` ((x `|` z) `<<` (W8.of_int 1)));
        state.[column] <- ((z `^` y) `^` ((x `&` y) `<<` (W8.of_int 3)));
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
        state.[0] <- (state.[0] `^` ((W32.of_int 2654435584) `^` (W32.of_int round)));
      } else {
        
      }
      round <- round - 1;
    }
    return (state);
  }
  
  proc gimli (istate:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    var state:W32.t Array12.t;
    state <- witness;
    i <- 0;
    while (i < 12) {
      state.[i] <- (loadW32 Glob.mem (W64.to_uint (istate + (W64.of_int (4 * i)))));
      i <- i + 1;
    }
    state <@ gimli_body (state);
    i <- 0;
    while (i < 12) {
      Glob.mem <- storeW32 Glob.mem (W64.to_uint (istate + (W64.of_int (4 * i)))) (state.[i]);
      i <- i + 1;
    }
    return ();
  }
}.

