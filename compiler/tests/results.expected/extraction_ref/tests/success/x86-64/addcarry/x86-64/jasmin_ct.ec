require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc add1 (arg:W64.t) : W64.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W64.t;
    
    var z:W64.t;
    var cf:bool;
    var _of_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var zf:bool;
    var cF:bool;
    var zF:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- arg;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z false;
     _0 <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z false;
    cf <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z cf;
     _1 <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z false;
     _2 <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z false;
     _3 <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z false;
    cf <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z false;
    cf <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z cf;
    cf <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux) <- adc_64 z z false;
    cf <- aux_4;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- ADC_64 z z cf;
     _4 <- aux_4;
    cf <- aux_3;
     _5 <- aux_2;
     _6 <- aux_1;
     _7 <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- ADC_64 z z cf;
    _of_ <- aux_4;
    cf <- aux_3;
    _sf_ <- aux_2;
     _8 <- aux_1;
    _zf_ <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- ADC_64 z z cf;
    _of_ <- aux_4;
    cf <- aux_3;
    _sf_ <- aux_2;
     _9 <- aux_1;
    _zf_ <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- ADC_64 z z cf;
    _of_ <- aux_4;
    cf <- aux_3;
    _sf_ <- aux_2;
     _10 <- aux_1;
    zf <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- ADC_64 z z cf;
    _of_ <- aux_4;
    cF <- aux_3;
    _sf_ <- aux_2;
     _11 <- aux_1;
    zF <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- ADC_64 z z cF;
     _12 <- aux_4;
     _13 <- aux_3;
     _14 <- aux_2;
     _15 <- aux_1;
     _16 <- aux_0;
    z <- aux;
    return (z);
  }
}.

