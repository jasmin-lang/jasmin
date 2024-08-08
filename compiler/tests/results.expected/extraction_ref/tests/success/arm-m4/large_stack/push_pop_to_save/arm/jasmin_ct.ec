require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array10 Array1024.
require import WArray40 WArray4096.



module M = {
  var leakages : leakages_t
  
  proc main () : W32.t = {
    var aux_1: int;
    var aux: W32.t;
    var aux_0: W32.t Array1024.t;
    
    var i:W32.t;
    var n:W32.t;
    var s:W32.t Array1024.t;
    var ps:W32.t Array1024.t;
    var j:int;
    var t:W32.t Array10.t;
    var d:W32.t;
    ps <- witness;
    s <- witness;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1024);
    n <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s;
    ps <- aux_0;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- i;
      leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
      ps.[(W32.to_uint i)] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W32.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 10) {
      leakages <- LeakAddr([j]) :: leakages;
      aux <- ps.[j];
      leakages <- LeakAddr([j]) :: leakages;
      t.[j] <- aux;
      j <- j + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 10);
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int ((1024 %/ 10) * 10));
    n <- aux;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
      j <- 0;
      while (j < 10) {
        leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
        aux <- ps.[(W32.to_uint i)];
        d <- aux;
        leakages <- LeakAddr([j]) :: leakages;
        aux <- (t.[j] + d);
        leakages <- LeakAddr([j]) :: leakages;
        t.[j] <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (i + (W32.of_int 1));
        i <- aux;
        j <- j + 1;
      }
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1024);
    n <- aux;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
      aux <- ps.[(W32.to_uint i)];
      d <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux <- (t.[0] + d);
      leakages <- LeakAddr([0]) :: leakages;
      t.[0] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W32.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakFor(1,10) :: LeakAddr([]) :: leakages;
    j <- 1;
    while (j < 10) {
      leakages <- LeakAddr([j; 0]) :: leakages;
      aux <- (t.[0] + t.[j]);
      leakages <- LeakAddr([0]) :: leakages;
      t.[0] <- aux;
      j <- j + 1;
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <- t.[0];
    i <- aux;
    return (i);
  }
}.

