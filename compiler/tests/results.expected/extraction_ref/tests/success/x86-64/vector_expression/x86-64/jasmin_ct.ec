require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc toto () : W64.t = {
    var aux_1: W64.t;
    var aux_0: W128.t;
    var aux: W256.t;
    
    var r:W64.t;
    var x:W256.t;
    var y:W256.t;
    var v:W128.t;
    var w:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W256.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W256.of_int 1);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vadd64u256 y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vadd64u256 y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vsub64u256 y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vsub64u256 y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vmul64u256 y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vmul64u256 y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vmul8u256 y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((W256.of_int 219) \vmul16u256 (W256.of_int 5));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vshl64u256 (W8.of_int 32));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vshr64u256 (W8.of_int 32));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vshl64u256 (W8.of_int 32));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vsar64u256 (W8.of_int 32));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x \vsar64u256 (W8.of_int 27));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W128.of_int 0);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W128.of_int 1);
    w <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vadd32u128 w);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vadd32u128 w);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vsub32u128 w);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vsub32u128 w);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vmul32u128 w);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vmul32u128 w);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vmul8u128 w);
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((W128.of_int 219) \vmul16u128 (W128.of_int 5));
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vshl32u128 (W8.of_int 32));
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vshr32u128 (W8.of_int 32));
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vshl32u128 (W8.of_int 32));
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (v \vsar32u128 (W8.of_int 32));
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W64.of_int 0);
    r <- aux_1;
    return (r);
  }
}.

