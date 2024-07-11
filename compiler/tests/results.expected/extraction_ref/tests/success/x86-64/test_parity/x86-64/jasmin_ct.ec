require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc case_0 (x:W64.t) : W64.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W64.t;
    
    var a:W64.t;
    var b:W64.t;
    var pf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0) <- TEST_64 x x;
     _0 <- aux_4;
     _1 <- aux_3;
     _2 <- aux_2;
    pf <- aux_1;
     _3 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (pf ? b : a);
    a <- aux;
    return (a);
  }
  
  proc test_parity () : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var result:W64.t;
    var i:int;
    var tmp:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    result <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int i);
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ case_0 (tmp);
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (result `<<` (W8.of_int 1));
      result <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (result `|` tmp);
      result <- aux;
      i <- i + 1;
    }
    return (result);
  }
}.

