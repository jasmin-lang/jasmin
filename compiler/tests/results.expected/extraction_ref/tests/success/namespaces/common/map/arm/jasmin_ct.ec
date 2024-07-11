require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array4.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc double__f (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `<<` (W8.of_int 1));
    x <- aux;
    return (x);
  }
  
  proc double__map (p:W32.t Array4.t) : W32.t Array4.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var i:int;
    var t:W32.t;
    
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- p.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ double__f (t);
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (p);
  }
  
  proc triple__f (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ double__f (y);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    x <- aux;
    return (x);
  }
  
  proc triple__map (p:W32.t Array4.t) : W32.t Array4.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var i:int;
    var t:W32.t;
    
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- p.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ triple__f (t);
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      p.[i] <- aux_0;
      i <- i + 1;
    }
    return (p);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux: int;
    var aux_0: W32.t;
    var aux_1: W32.t Array4.t;
    
    var r:W32.t;
    var i:int;
    var s:W32.t Array4.t;
    s <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- a;
      leakages <- LeakAddr([i]) :: leakages;
      s.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ double__map (s);
    s <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ triple__map (s);
    s <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    r <- aux_0;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- s.[i];
      a <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (r + a);
      r <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
}.

