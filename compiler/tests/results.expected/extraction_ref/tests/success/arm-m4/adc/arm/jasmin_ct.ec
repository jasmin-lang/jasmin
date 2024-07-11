require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc adc (arg0:W32.t, arg1:W32.t) : W32.t = {
    var aux_0: bool;
    var aux: W32.t;
    
    var res_0:W32.t;
    var x:W32.t;
    var c:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- arg1;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 arg0 x false;
     _0 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 arg0 x false;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x (W32.of_int 12) false;
     _1 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x (W32.of_int 98) false;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 arg0 x c;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 arg0 x c;
     _2 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 arg0 x false;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 arg0 x false;
     _3 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x arg0 false;
     _4 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x arg0 false;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x (W32.of_int 12) false;
     _5 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x (W32.of_int 98) false;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x arg0 c;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x arg0 c;
     _6 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x arg0 false;
    c <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_32 x arg0 false;
     _7 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    res_0 <- aux;
    return (res_0);
  }
}.

