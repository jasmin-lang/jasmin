require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test1 () : int = {
    var aux: int;
    
    var j:int;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- 0;
    j <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (j + i);
      j <- aux;
      i <- i + 1;
    }
    return (j);
  }
  
  proc test2 () : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var j:W64.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    j <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (j + (W64.of_int i));
      j <- aux;
      i <- i + 1;
    }
    return (j);
  }
  
  proc test3 () : W64.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var j:W64.t;
    var tmp:int;
    var i:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test1 ();
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int tmp);
    j <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ test2 ();
    i <- aux_0;
    
    leakages <- LeakCond((j \ule (W64.of_int 12))) :: LeakAddr([]) :: leakages;
    
    while ((j \ule (W64.of_int 12))) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (j + i);
      j <- aux_0;
    leakages <- LeakCond((j \ule (W64.of_int 12))) :: LeakAddr([]) :: leakages;
    
    }
    return (j);
  }
}.

