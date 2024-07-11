require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array12.
require import WArray48.



module M = {
  var leakages : leakages_t
  
  proc swap_0 (state:W32.t Array12.t, i:int, j:int) : W32.t Array12.t = {
    var aux: W32.t;
    
    var x:W32.t;
    var y:W32.t;
    
    leakages <- LeakAddr([i]) :: leakages;
    aux <- state.[i];
    x <- aux;
    leakages <- LeakAddr([j]) :: leakages;
    aux <- state.[j];
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    leakages <- LeakAddr([i]) :: leakages;
    state.[i] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([j]) :: leakages;
    state.[j] <- aux;
    return (state);
  }
  
  proc gimli (state:W32.t Array12.t) : W32.t Array12.t = {
    var aux_0: int;
    var aux: W32.t;
    var aux_1: W32.t Array12.t;
    
    var rc:W32.t;
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var a:W32.t;
    var b:W32.t;
    var round:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 2654435584);
    rc <- aux;
    leakages <- LeakFor(24,0) :: LeakAddr([]) :: leakages;
    round <- 24;
    while (0 < round) {
      leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
      column <- 0;
      while (column < 4) {
        leakages <- LeakAddr([(0 + column)]) :: leakages;
        aux <- state.[(0 + column)];
        x <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (x `|<<|` (W8.of_int 24));
        x <- aux;
        leakages <- LeakAddr([(4 + column)]) :: leakages;
        aux <- state.[(4 + column)];
        y <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (y `|<<|` (W8.of_int 9));
        y <- aux;
        leakages <- LeakAddr([(8 + column)]) :: leakages;
        aux <- state.[(8 + column)];
        z <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (x `^` (z `<<` (W8.of_int 1)));
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (y `&` z);
        b <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (a `^` (b `<<` (W8.of_int 2)));
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- a;
        leakages <- LeakAddr([(8 + column)]) :: leakages;
        state.[(8 + column)] <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (y `^` x);
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (x `|` z);
        b <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (a `^` (b `<<` (W8.of_int 1)));
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- a;
        leakages <- LeakAddr([(4 + column)]) :: leakages;
        state.[(4 + column)] <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (z `^` y);
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (x `&` y);
        b <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (a `^` (b `<<` (W8.of_int 3)));
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- a;
        leakages <- LeakAddr([(0 + column)]) :: leakages;
        state.[(0 + column)] <- aux;
        column <- column + 1;
      }
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ swap_0 (state, 0, 1);
        state <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ swap_0 (state, 2, 3);
        state <- aux_1;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 2)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 2)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ swap_0 (state, 0, 2);
        state <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ swap_0 (state, 1, 3);
        state <- aux_1;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakAddr([0]) :: leakages;
        aux <- state.[0];
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (rc + (W32.of_int round));
        b <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (a `^` b);
        a <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- a;
        leakages <- LeakAddr([0]) :: leakages;
        state.[0] <- aux;
      } else {
        
      }
      round <- round - 1;
    }
    return (state);
  }
}.

