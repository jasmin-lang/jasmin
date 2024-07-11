require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc add (arg0:W32.t, arg1:W32.t) : W32.t = {
    var aux: W32.t;
    
    var x:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- arg1;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (arg0 + (x `<<` (W8.of_int 3)));
    x <- aux;
    return (x);
  }
  
  proc main (arg0:W32.t, arg1:W32.t) : W32.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_3: int;
    var aux_2: W32.t;
    
    var x:W32.t;
    var z:bool;
    var y:W32.t;
    var n:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0, aux, aux_2) <- MOVS arg0;
     _0 <- aux_1;
    z <- aux_0;
     _1 <- aux;
    x <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- arg1;
    y <- aux_2;
    leakages <- LeakCond(z) :: LeakAddr([]) :: leakages;
    if (z) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ add (x, y);
      x <- aux_2;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ add (x, y);
      x <- aux_2;
    }
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    n <- 0;
    while (n < 3) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ add (x, y);
      x <- aux_2;
      n <- n + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0, aux, aux_2) <- MOVS x;
     _2 <- aux_1;
    z <- aux_0;
     _3 <- aux;
     _4 <- aux_2;
    leakages <- LeakCond(z) :: LeakAddr([]) :: leakages;
    
    while (z) {
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <@ add (x, y);
      x <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux_0, aux, aux_2) <- MOVS x;
       _2 <- aux_1;
      z <- aux_0;
       _3 <- aux;
       _4 <- aux_2;
    leakages <- LeakCond(z) :: LeakAddr([]) :: leakages;
    
    }
    return (x);
  }
}.

