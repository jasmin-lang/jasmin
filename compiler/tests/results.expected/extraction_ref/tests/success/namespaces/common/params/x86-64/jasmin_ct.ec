require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array8.
require import WArray4 WArray32.



module M = {
  var leakages : leakages_t
  
  proc short__sum (t:W32.t Array1.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var s:W32.t;
    var c:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    s <- aux;
    leakages <- LeakFor(0,1) :: LeakAddr([]) :: leakages;
    c <- 0;
    while (c < 1) {
      leakages <- LeakAddr([c]) :: leakages;
      aux <- (s + t.[c]);
      s <- aux;
      c <- c + 1;
    }
    return (s);
  }
  
  proc long__sum (t:W32.t Array8.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var s:W32.t;
    var c:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    s <- aux;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    c <- 0;
    while (c < 8) {
      leakages <- LeakAddr([c]) :: leakages;
      aux <- (s + t.[c]);
      s <- aux;
      c <- c + 1;
    }
    return (s);
  }
  
  proc test (a:W32.t) : W32.t = {
    var aux: int;
    var aux_0: W32.t;
    
    var r:W32.t;
    var i:int;
    var x:W32.t Array1.t;
    var y:W32.t Array8.t;
    var t:W32.t;
    x <- witness;
    y <- witness;
    leakages <- LeakFor(0,1) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 1) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- a;
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- a;
      leakages <- LeakAddr([i]) :: leakages;
      y.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ short__sum (x);
    t <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (r + t);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ long__sum (y);
    t <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (r + t);
    r <- aux_0;
    return (r);
  }
}.

