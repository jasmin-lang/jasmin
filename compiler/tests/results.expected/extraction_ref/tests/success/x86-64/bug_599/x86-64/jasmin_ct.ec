require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (a:W64.t, b:W64.t) : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var res_0:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cond:bool;
    var one:W64.t;
    var  _0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux) <- CMP_64 a b;
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _0 <- aux_0;
    _zf_ <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_NEQ _of_ _cf_ _sf_ _zf_);
    cond <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (W64.of_int 0);
    res_0 <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (W64.of_int 1);
    one <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (cond ? one : res_0);
    res_0 <- aux_4;
    return (res_0);
  }
}.

