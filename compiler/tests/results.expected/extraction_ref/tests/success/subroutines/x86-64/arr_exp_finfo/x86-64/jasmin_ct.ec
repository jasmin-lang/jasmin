require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc test1 (t:W64.t Array2.t, p:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (t.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (p.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (p, t);
  }
  
  proc test2 (t:W64.t Array2.t, p:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (t.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (p.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (t, p);
  }
  
  proc test3 (p:W64.t Array2.t, t:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (t.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (p.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (p, t);
  }
  
  proc test4 (p:W64.t Array2.t, t:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (t.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (p.[i] + (W64.of_int 1));
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (t, p);
  }
  
  proc main () : W64.t = {
    var aux_0: int;
    var aux_1: W64.t;
    var aux_2: W64.t Array2.t;
    var aux: W64.t Array2.t;
    
    var r:W64.t;
    var s:W64.t Array2.t;
    var p:W64.t Array2.t;
    var i:int;
    var t:W64.t Array2.t;
    p <- witness;
    s <- witness;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- s;
    p <- aux_2;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux) <@ test1 (t, p);
    p <- aux_2;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux) <@ test2 (t, p);
    t <- aux_2;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux) <@ test3 (p, t);
    p <- aux_2;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux) <@ test4 (p, t);
    t <- aux_2;
    p <- aux;
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux_1 <- (t.[0] + t.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    leakages <- LeakAddr([0; 0]) :: leakages;
    aux_1 <- (t.[0] + p.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux_1 <- (t.[0] + p.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- t.[0];
    r <- aux_1;
    return (r);
  }
}.

