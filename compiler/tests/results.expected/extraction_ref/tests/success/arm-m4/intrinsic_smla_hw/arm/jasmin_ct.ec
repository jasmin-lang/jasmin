require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc smla_hw (x:W32.t, y:W32.t, acc:W32.t) : W32.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W32.t;
    
    var r:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLABB x y acc;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLABT x y r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLATB x y r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLATT x y r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP x y;
    _nf_ <- aux_3;
    _zf_ <- aux_2;
    _cf_ <- aux_1;
    _vf_ <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_sLT _nf_ _zf_ _cf_ _vf_);
    b <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLABBcc x y r b r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLABTcc x y r b r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLATBcc x y r b r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SMLATTcc x y r b r;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    r <- aux;
    return (r);
  }
}.

