require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array12.
require import WArray48.



module M = {
  var leakages : leakages_t
  
  proc gimli (state:W32.t Array12.t) : W32.t Array12.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var round:int;
    
    leakages <- LeakFor(24,0) :: LeakAddr([]) :: leakages;
    round <- 24;
    while (0 < round) {
      leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
      column <- 0;
      while (column < 4) {
        leakages <- LeakAddr([(0 + column)]) :: leakages;
        aux_0 <- state.[(0 + column)];
        x <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (x `|<<|` (W8.of_int 24));
        x <- aux_0;
        leakages <- LeakAddr([(4 + column)]) :: leakages;
        aux_0 <- state.[(4 + column)];
        y <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (y `|<<|` (W8.of_int 9));
        y <- aux_0;
        leakages <- LeakAddr([(8 + column)]) :: leakages;
        aux_0 <- state.[(8 + column)];
        z <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- z;
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (b `<<` (W8.of_int 1));
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- y;
        c <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (c `&` z);
        c <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (c `<<` (W8.of_int 2));
        c <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (a `^` b);
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (a `^` c);
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- a;
        leakages <- LeakAddr([(8 + column)]) :: leakages;
        state.[(8 + column)] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- y;
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (b `|` z);
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (b `<<` (W8.of_int 1));
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (a `^` x);
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (a `^` b);
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- a;
        leakages <- LeakAddr([(4 + column)]) :: leakages;
        state.[(4 + column)] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- z;
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (b `&` y);
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (b `<<` (W8.of_int 3));
        b <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (a `^` y);
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (a `^` b);
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- a;
        leakages <- LeakAddr([(0 + column)]) :: leakages;
        state.[(0 + column)] <- aux_0;
        column <- column + 1;
      }
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakAddr([0]) :: leakages;
        aux_0 <- state.[0];
        x <- aux_0;
        leakages <- LeakAddr([1]) :: leakages;
        aux_0 <- state.[1];
        y <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- y;
        leakages <- LeakAddr([0]) :: leakages;
        state.[0] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        leakages <- LeakAddr([1]) :: leakages;
        state.[1] <- aux_0;
        leakages <- LeakAddr([2]) :: leakages;
        aux_0 <- state.[2];
        x <- aux_0;
        leakages <- LeakAddr([3]) :: leakages;
        aux_0 <- state.[3];
        y <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- y;
        leakages <- LeakAddr([2]) :: leakages;
        state.[2] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        leakages <- LeakAddr([3]) :: leakages;
        state.[3] <- aux_0;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 2)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 2)) {
        leakages <- LeakAddr([0]) :: leakages;
        aux_0 <- state.[0];
        x <- aux_0;
        leakages <- LeakAddr([2]) :: leakages;
        aux_0 <- state.[2];
        y <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- y;
        leakages <- LeakAddr([0]) :: leakages;
        state.[0] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        leakages <- LeakAddr([2]) :: leakages;
        state.[2] <- aux_0;
        leakages <- LeakAddr([1]) :: leakages;
        aux_0 <- state.[1];
        x <- aux_0;
        leakages <- LeakAddr([3]) :: leakages;
        aux_0 <- state.[3];
        y <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- y;
        leakages <- LeakAddr([1]) :: leakages;
        state.[1] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- x;
        leakages <- LeakAddr([3]) :: leakages;
        state.[3] <- aux_0;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakAddr([0]) :: leakages;
        aux_0 <- (state.[0] `^` (W32.of_int (2654435584 + round)));
        leakages <- LeakAddr([0]) :: leakages;
        state.[0] <- aux_0;
      } else {
        
      }
      round <- round - 1;
    }
    return (state);
  }
}.

