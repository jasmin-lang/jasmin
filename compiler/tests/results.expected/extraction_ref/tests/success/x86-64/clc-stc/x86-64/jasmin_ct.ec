require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_stc () : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _0 <- aux_0;
    _zf_ <- aux;
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- STC ;
    cf <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_4) <- adc_64 r r cf;
     _1 <- aux_3;
    r <- aux_4;
    return (r);
  }
  
  proc test_clc () : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _0 <- aux_0;
    _zf_ <- aux;
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- CLC ;
    cf <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_4) <- adc_64 r r cf;
     _1 <- aux_3;
    r <- aux_4;
    return (r);
  }
}.

