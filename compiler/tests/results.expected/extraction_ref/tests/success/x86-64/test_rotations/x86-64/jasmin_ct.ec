require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : W64.t = {
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: W8.t;
    var aux: W64.t;
    
    var c:W64.t;
    var a:W64.t;
    var d:W8.t;
    var of_0:bool;
    var cf:bool;
    var b:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W8.of_int 4);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a `|<<|` (d `&` (W8.of_int 63)));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a `|<<|` (W8.of_int 2));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux) <- ROL_64 a d;
     _0 <- aux_2;
     _1 <- aux_1;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux) <- ROL_64 a (W8.of_int 2);
    of_0 <- aux_2;
    cf <- aux_1;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux) <- adc_64 b x cf;
    cf <- aux_2;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (b `|>>|` (d `&` (W8.of_int 63)));
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (b `|>>|` (W8.of_int 3));
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux) <- ROR_64 b d;
     _2 <- aux_2;
     _3 <- aux_1;
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux) <- ROR_64 c (W8.of_int 3);
     _4 <- aux_2;
     _5 <- aux_1;
    c <- aux;
    return (c);
  }
}.

