require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_while (x:W64.t) : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var i:W64.t;
    var zf:bool;
    var _of_:bool;
    var _sf_:bool;
    var  _0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 10);
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (W64.of_int 1));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux) <- DEC_64 i;
    _of_ <- aux_3;
    _sf_ <- aux_2;
     _0 <- aux_1;
    zf <- aux_0;
    i <- aux;
    leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
    
    while ((! zf)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (r + (W64.of_int 2));
      r <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (r + (W64.of_int 1));
      r <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_3, aux_2, aux_1, aux_0, aux) <- DEC_64 i;
      _of_ <- aux_3;
      _sf_ <- aux_2;
       _0 <- aux_1;
      zf <- aux_0;
      i <- aux;
    leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    return (r);
  }
  
  proc zero (y:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var x:W64.t;
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x \slt (W64.of_int 0));
    b <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    while (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (x + (W64.of_int 1));
      x <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (x \slt (W64.of_int 0));
      b <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    }
    return (x);
  }
}.

