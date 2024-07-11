require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array8.
require import WArray8 WArray64.



module M = {
  var leakages : leakages_t
  
  proc test0 (x:W64.t) : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var result:W64.t;
    var i:int;
    var tab:W64.t Array8.t;
    tab <- witness;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- x;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    result <- aux_0;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (result + tab.[i]);
      result <- aux_0;
      i <- i + 1;
    }
    return (result);
  }
  
  proc test1 (x:W64.t) : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var result:W64.t;
    var t:W64.t;
    var i:int;
    var tab:W64.t Array8.t;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    result <- aux;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (result + tab.[i]);
      result <- aux;
      i <- i + 1;
    }
    return (result);
  }
  
  proc test2 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    var t:W64.t Array1.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- t.[0];
    result <- aux;
    return (result);
  }
  
  proc copy (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var t:W64.t Array1.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- t.[0];
    x <- aux;
    return (x);
  }
  
  proc test3 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy (x);
    result <- aux;
    return (result);
  }
  
  proc test4 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy (x);
    result <- aux;
    return (result);
  }
  
  proc test5 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy (x);
    result <- aux;
    return (result);
  }
  
  proc test6 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy (x);
    result <- aux;
    return (result);
  }
}.

