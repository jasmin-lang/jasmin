require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc lzcnt (x:W64.t) : W64.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var _of_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var  _0:bool;
    var  _1:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux) <- DEC_64 r;
    _of_ <- aux_4;
    _sf_ <- aux_3;
     _0 <- aux_2;
    _zf_ <- aux_1;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- LZCNT_64 x;
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _1 <- aux_1;
    _zf_ <- aux_0;
    r <- aux;
    return (r);
  }
  
  proc foo () : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var a:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int (1 `<<` 62));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ lzcnt (a);
    r <- aux;
    return (r);
  }
}.

