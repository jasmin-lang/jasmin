require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array1 Array4 Array5 Array13.
require import WArray4 WArray16 WArray20 WArray52.



module M = {
  var leakages : leakages_t
  
  proc onregister0 (x:W32.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array1.t;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakFor(0,1) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 1) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    result <- aux;
    leakages <- LeakFor(0,1) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 1) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (result + tab.[i]);
      result <- aux;
      i <- i + 1;
    }
    return (result);
  }
  
  proc onregister1 (x:W32.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array4.t;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakFor(0,(((14 - 8) - 1) - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- (((14 - 8) - 1) - 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    result <- aux;
    leakages <- LeakFor(0,(((14 - 8) - 1) - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- (((14 - 8) - 1) - 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (result + tab.[i]);
      result <- aux;
      i <- i + 1;
    }
    return (result);
  }
  
  proc onstack0 (x:W32.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array5.t;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakFor(0,((14 - 8) - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- ((14 - 8) - 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    result <- aux;
    leakages <- LeakFor(0,((14 - 8) - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- ((14 - 8) - 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (result + tab.[i]);
      result <- aux;
      i <- i + 1;
    }
    return (result);
  }
  
  proc onstack1 (x:W32.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array13.t;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakFor(0,(14 - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- (14 - 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    result <- aux;
    leakages <- LeakFor(0,(14 - 1)) :: LeakAddr([]) :: leakages;
    aux_0 <- (14 - 1);
    i <- 0;
    while (i < aux_0) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (result + tab.[i]);
      result <- aux;
      i <- i + 1;
    }
    return (result);
  }
}.

