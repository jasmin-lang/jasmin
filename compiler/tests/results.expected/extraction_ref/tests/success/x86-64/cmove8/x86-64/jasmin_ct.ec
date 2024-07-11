require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (b:W8.t, x:W64.t, y:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var c:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (b = (W8.of_int 1));
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x \slt y);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x \ult y);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x \sle y);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x \ule y);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x = y);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (y \ule x);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (y \sle x);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (y \ult x);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (y \slt x);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    return (r);
  }
  
  proc g (x:W64.t, y:W64.t) : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_5: W8.t;
    var aux_4: W64.t;
    
    var r:W64.t;
    var of_0:bool;
    var cf:bool;
    var sf:bool;
    var zf:bool;
    var b0:bool;
    var c:bool;
    var b1:bool;
    var b2:bool;
    var z:W8.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    var  _1:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux) <- CMP_64 x y;
    of_0 <- aux_3;
    cf <- aux_2;
    sf <- aux_1;
     _0 <- aux_0;
    zf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_EQ of_0 cf sf zf);
    b0 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_sLT of_0 cf sf zf);
    c <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_uLT of_0 cf sf zf);
    b1 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_uGT of_0 cf sf zf);
    b2 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (b0 ? y : r);
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (b1 ? y : r);
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- SETcc b1;
    z <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (zeroextu64 z);
    x <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (b2 ? y : r);
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (r + x);
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux) <- CMP_64 x y;
    _of_ <- aux_3;
    _cf_ <- aux_2;
    _sf_ <- aux_1;
     _1 <- aux_0;
    _zf_ <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_EQ _of_ _cf_ _sf_ _zf_);
    b0 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_sLT _of_ _cf_ _sf_ _zf_);
    c <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- (_uLT _of_ _cf_ _sf_ _zf_);
    b1 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (b0 ? y : r);
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (b1 ? y : r);
    r <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- SETcc b1;
    z <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (zeroextu64 z);
    x <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- (r + x);
    r <- aux_4;
    return (r);
  }
}.

