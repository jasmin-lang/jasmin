require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array12.
require import WArray48.



module M = {
  var leakages : leakages_t
  
  proc rotate (x:W32.t, bits:int) : W32.t = {
    var aux_0: bool;
    var aux: bool;
    var aux_1: W32.t;
    
    var  _0:bool;
    var  _1:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux, aux_1) <- ROL_32 x (W8.of_int bits);
     _0 <- aux_0;
     _1 <- aux;
    x <- aux_1;
    return (x);
  }
  
  proc gimli_body (state:W32.t Array12.t) : W32.t Array12.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var column:int;
    var x:W32.t;
    var y:W32.t;
    var z:W32.t;
    var round:int;
    
    leakages <- LeakFor(24,0) :: LeakAddr([]) :: leakages;
    round <- 24;
    while (0 < round) {
      leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
      column <- 0;
      while (column < 4) {
        leakages <- LeakAddr([column]) :: leakages;
        aux_0 <- state.[column];
        x <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <@ rotate (x, 24);
        x <- aux_0;
        leakages <- LeakAddr([(4 + column)]) :: leakages;
        aux_0 <- state.[(4 + column)];
        y <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <@ rotate (y, 9);
        y <- aux_0;
        leakages <- LeakAddr([(8 + column)]) :: leakages;
        aux_0 <- state.[(8 + column)];
        z <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- ((x `^` (z `<<` (W8.of_int 1))) `^` ((y `&` z) `<<` (W8.of_int 2)));
        leakages <- LeakAddr([(8 + column)]) :: leakages;
        state.[(8 + column)] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- ((y `^` x) `^` ((x `|` z) `<<` (W8.of_int 1)));
        leakages <- LeakAddr([(4 + column)]) :: leakages;
        state.[(4 + column)] <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- ((z `^` y) `^` ((x `&` y) `<<` (W8.of_int 3)));
        leakages <- LeakAddr([column]) :: leakages;
        state.[column] <- aux_0;
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
        aux_0 <- (state.[0] `^` ((W32.of_int 2654435584) `^` (W32.of_int round)));
        leakages <- LeakAddr([0]) :: leakages;
        state.[0] <- aux_0;
      } else {
        
      }
      round <- round - 1;
    }
    return (state);
  }
  
  proc gimli (istate:W64.t) : unit = {
    var aux: int;
    var aux_0: W32.t;
    var aux_1: W32.t Array12.t;
    
    var i:int;
    var state:W32.t Array12.t;
    state <- witness;
    leakages <- LeakFor(0,12) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 12) {
      leakages <- LeakAddr([(W64.to_uint (istate + (W64.of_int (4 * i))))]) :: leakages;
      aux_0 <- (loadW32 Glob.mem (W64.to_uint (istate + (W64.of_int (4 * i)))));
      leakages <- LeakAddr([i]) :: leakages;
      state.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ gimli_body (state);
    state <- aux_1;
    leakages <- LeakFor(0,12) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 12) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- state.[i];
      leakages <- LeakAddr([(W64.to_uint (istate + (W64.of_int (4 * i))))]) :: leakages;
      Glob.mem <- storeW32 Glob.mem (W64.to_uint (istate + (W64.of_int (4 * i)))) (aux_0);
      i <- i + 1;
    }
    return ();
  }
}.

