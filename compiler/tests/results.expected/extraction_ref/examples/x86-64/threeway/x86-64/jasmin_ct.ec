require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc threeway (x:W64.t) : W64.t = {
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
    var below:bool;
    var equal:bool;
    var  _0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux) <- CMP_64 x (W64.of_int 2);
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _0 <- aux_0;
    _zf_ <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_uLT _of_ _cf_ _sf_ _zf_);
    below <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_EQ _of_ _cf_ _sf_ _zf_);
    equal <- aux_3;
    leakages <- LeakCond(below) :: LeakAddr([]) :: leakages;
    if (below) {
      leakages <- LeakAddr([]) :: leakages;
      aux_4 <- (W64.of_int 1);
      r <- aux_4;
    } else {
      leakages <- LeakCond(equal) :: LeakAddr([]) :: leakages;
      if (equal) {
        leakages <- LeakAddr([]) :: leakages;
        aux_4 <- (W64.of_int 2);
        r <- aux_4;
      } else {
        leakages <- LeakAddr([]) :: leakages;
        aux_4 <- (W64.of_int 3);
        r <- aux_4;
      }
    }
    return (r);
  }
}.

