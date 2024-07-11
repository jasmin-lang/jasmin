require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array17.
require import WArray68.



module M = {
  var leakages : leakages_t
  
  proc use (t:W32.t Array17.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var s:W32.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    s <- aux;
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 17) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (s + t.[i]);
      s <- aux;
      i <- i + 1;
    }
    return (s);
  }
  
  proc copy (in_0:W64.t, inlen:W64.t) : W32.t = {
    var aux_7: bool;
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: int;
    var aux_0: W8.t;
    var aux: W32.t;
    var aux_1: W64.t;
    
    var r:W32.t;
    var one:W32.t;
    var size:W8.t;
    var tmp:W32.t;
    var i:int;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var eq:bool;
    var le:bool;
    var t:W32.t Array17.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1);
    one <- aux;
    
    leakages <- LeakCond(((W64.of_int 0) \slt inlen)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \slt inlen)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- inlen;
      size <- (truncateu8 aux_1);
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (size `&` (W8.of_int 15));
      size <- aux_0;
      leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
      i <- 0;
      while (i < 17) {
        leakages <- LeakAddr([]) :: leakages;
        (aux_7, aux_6, aux_5, aux_4, aux_3, aux) <- set0_32 ;
         _0 <- aux_7;
         _1 <- aux_6;
         _2 <- aux_5;
         _3 <- aux_4;
         _4 <- aux_3;
        tmp <- aux;
        leakages <- LeakAddr([]) :: leakages;
        (aux_7, aux_6, aux_5, aux_4, aux_3) <- CMP_8 size (W8.of_int i);
        _of_ <- aux_7;
        _cf_ <- aux_6;
        _sf_ <- aux_5;
         _5 <- aux_4;
        _zf_ <- aux_3;
        leakages <- LeakAddr([]) :: leakages;
        aux_7 <- (_EQ _of_ _cf_ _sf_ _zf_);
        eq <- aux_7;
        leakages <- LeakAddr([]) :: leakages;
        aux_7 <- (_sLE _of_ _cf_ _sf_ _zf_);
        le <- aux_7;
        leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int i)))]) :: leakages;
        aux <- ((! le) ? (loadW32 Glob.mem (W64.to_uint (in_0 + (W64.of_int i)))) : tmp);
        tmp <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (eq ? one : tmp);
        tmp <- aux;
        leakages <- LeakAddr([]) :: leakages;
        aux <- tmp;
        leakages <- LeakAddr([i]) :: leakages;
        t.[i] <- aux;
        i <- i + 1;
      }
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (in_0 + (W64.of_int 16));
      in_0 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (inlen - (W64.of_int 16));
      inlen <- aux_1;
    leakages <- LeakCond(((W64.of_int 0) \slt inlen)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <@ use (t);
    r <- aux;
    return (r);
  }
}.

