require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_conditions (x:W32.t, y:W32.t) : W32.t = {
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_3: W32.t;
    
    var r:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var eq:bool;
    var neq:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0, aux) <- CMP x y;
    _nf_ <- aux_2;
    _zf_ <- aux_1;
    _cf_ <- aux_0;
    _vf_ <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (_EQ _nf_ _zf_ _cf_ _vf_);
    eq <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (_NEQ _nf_ _zf_ _cf_ _vf_);
    neq <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (W32.of_int 0);
    r <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (eq ? x : r);
    r <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (neq ? y : r);
    r <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- r;
    r <- aux_3;
    return (r);
  }
}.

