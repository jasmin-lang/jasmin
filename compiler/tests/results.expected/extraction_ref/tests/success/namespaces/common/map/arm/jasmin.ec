require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array4.
require import WArray16.



module M = {
  proc double__f (x:W32.t) : W32.t = {
    
    
    
    x <- (x `<<` (W8.of_int 1));
    return (x);
  }
  
  proc double__map (p:W32.t Array4.t) : W32.t Array4.t = {
    var aux: int;
    
    var i:int;
    var t:W32.t;
    
    i <- 0;
    while (i < 4) {
      t <- p.[i];
      t <@ double__f (t);
      p.[i] <- t;
      i <- i + 1;
    }
    return (p);
  }
  
  proc triple__f (x:W32.t) : W32.t = {
    
    var y:W32.t;
    
    y <- x;
    y <@ double__f (y);
    x <- (x + y);
    return (x);
  }
  
  proc triple__map (p:W32.t Array4.t) : W32.t Array4.t = {
    var aux: int;
    
    var i:int;
    var t:W32.t;
    
    i <- 0;
    while (i < 4) {
      t <- p.[i];
      t <@ triple__f (t);
      p.[i] <- t;
      i <- i + 1;
    }
    return (p);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux: int;
    
    var r:W32.t;
    var i:int;
    var s:W32.t Array4.t;
    s <- witness;
    i <- 0;
    while (i < 4) {
      s.[i] <- a;
      i <- i + 1;
    }
    s <@ double__map (s);
    s <@ triple__map (s);
    r <- (W32.of_int 0);
    i <- 0;
    while (i < 4) {
      a <- s.[i];
      r <- (r + a);
      i <- i + 1;
    }
    return (r);
  }
}.

