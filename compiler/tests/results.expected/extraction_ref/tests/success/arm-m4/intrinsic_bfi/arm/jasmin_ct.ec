require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc bfi (x:W32.t) : W32.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W32.t;
    
    var y:W32.t;
    var _nf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var _vf_:bool;
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- BFI y x (W8.of_int 0) (W8.of_int 1);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- BFI y x (W8.of_int 31) (W8.of_int 1);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- BFI y x (W8.of_int 0) (W8.of_int 32);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP y (W32.of_int 5);
    _nf_ <- aux_3;
    _zf_ <- aux_2;
    _cf_ <- aux_1;
    _vf_ <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_sLT _nf_ _zf_ _cf_ _vf_);
    b <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux <- BFIcc y x (W8.of_int 0) (W8.of_int 32) b y;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    y <- aux;
    return (y);
  }
}.

