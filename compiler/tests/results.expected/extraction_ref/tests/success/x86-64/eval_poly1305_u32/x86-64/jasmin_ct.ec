require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array17.
require import WArray68.



module M = {
  var leakages : leakages_t
  
  proc add (h:W32.t Array17.t, c:W32.t Array17.t) : W32.t Array17.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    u <- aux;
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 17) {
      leakages <- LeakAddr([j]) :: leakages;
      aux <- (u + h.[j]);
      u <- aux;
      leakages <- LeakAddr([j]) :: leakages;
      aux <- (u + c.[j]);
      u <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- u;
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp `&` (W32.of_int 255));
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- tmp;
      leakages <- LeakAddr([j]) :: leakages;
      h.[j] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (u `>>` (W8.of_int 8));
      u <- aux;
      j <- j + 1;
    }
    return (h);
  }
  
  proc add_minusp (h:W32.t Array17.t) : W32.t Array17.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    u <- aux;
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 17) {
      leakages <- LeakAddr([j]) :: leakages;
      aux <- (u + h.[j]);
      u <- aux;
      leakages <- LeakCond((j = 0)) :: LeakAddr([]) :: leakages;
      if ((j = 0)) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (u + (W32.of_int 5));
        u <- aux;
      } else {
        
      }
      leakages <- LeakCond((j = 16)) :: LeakAddr([]) :: leakages;
      if ((j = 16)) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (u + (W32.of_int 252));
        u <- aux;
      } else {
        
      }
      leakages <- LeakAddr([]) :: leakages;
      aux <- u;
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp `&` (W32.of_int 255));
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- tmp;
      leakages <- LeakAddr([j]) :: leakages;
      h.[j] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (u `>>` (W8.of_int 8));
      u <- aux;
      j <- j + 1;
    }
    return (h);
  }
  
  proc add_and_store (out:W64.t, h:W32.t Array17.t, c:W32.t Array17.t) : unit = {
    var aux_0: int;
    var aux_1: W8.t;
    var aux: W32.t;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    u <- aux;
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 16) {
      leakages <- LeakAddr([j]) :: leakages;
      aux <- (u + h.[j]);
      u <- aux;
      leakages <- LeakAddr([j]) :: leakages;
      aux <- (u + c.[j]);
      u <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- u;
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp `&` (W32.of_int 255));
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- tmp;
      leakages <- LeakAddr([(W64.to_uint (out + (W64.of_int j)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + (W64.of_int j))) ((truncateu8 aux));
      leakages <- LeakAddr([]) :: leakages;
      aux <- (u `>>` (W8.of_int 8));
      u <- aux;
      j <- j + 1;
    }
    return ();
  }
  
  proc freeze (h:W32.t Array17.t) : W32.t Array17.t = {
    var aux: int;
    var aux_0: W32.t;
    var aux_1: W32.t Array17.t;
    
    var j:int;
    var tmp:W32.t;
    var horig:W32.t Array17.t;
    var negative:W32.t;
    horig <- witness;
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 17) {
      leakages <- LeakAddr([j]) :: leakages;
      aux_0 <- h.[j];
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- tmp;
      leakages <- LeakAddr([j]) :: leakages;
      horig.[j] <- aux_0;
      j <- j + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ add_minusp (h);
    h <- aux_1;
    leakages <- LeakAddr([16]) :: leakages;
    aux_0 <- h.[16];
    negative <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (negative `>>` (W8.of_int 7));
    negative <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (- negative);
    negative <- aux_0;
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 17) {
      leakages <- LeakAddr([j]) :: leakages;
      aux_0 <- horig.[j];
      tmp <- aux_0;
      leakages <- LeakAddr([j]) :: leakages;
      aux_0 <- (tmp `^` h.[j]);
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (tmp `&` negative);
      tmp <- aux_0;
      leakages <- LeakAddr([j]) :: leakages;
      aux_0 <- (h.[j] `^` tmp);
      leakages <- LeakAddr([j]) :: leakages;
      h.[j] <- aux_0;
      j <- j + 1;
    }
    return (h);
  }
  
  proc squeeze (h:W32.t Array17.t) : W32.t Array17.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    u <- aux;
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 16) {
      leakages <- LeakAddr([j]) :: leakages;
      aux <- (u + h.[j]);
      u <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- u;
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp `&` (W32.of_int 255));
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- tmp;
      leakages <- LeakAddr([j]) :: leakages;
      h.[j] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (u `>>` (W8.of_int 8));
      u <- aux;
      j <- j + 1;
    }
    leakages <- LeakAddr([16]) :: leakages;
    aux <- (u + h.[16]);
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- u;
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (tmp `&` (W32.of_int 3));
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- tmp;
    leakages <- LeakAddr([16]) :: leakages;
    h.[16] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (u `>>` (W8.of_int 2));
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (u * (W32.of_int 5));
    u <- aux;
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 16) {
      leakages <- LeakAddr([j]) :: leakages;
      aux <- (u + h.[j]);
      u <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- u;
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (tmp `&` (W32.of_int 255));
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- tmp;
      leakages <- LeakAddr([j]) :: leakages;
      h.[j] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (u `>>` (W8.of_int 8));
      u <- aux;
      j <- j + 1;
    }
    leakages <- LeakAddr([16]) :: leakages;
    aux <- (u + h.[16]);
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- u;
    leakages <- LeakAddr([16]) :: leakages;
    h.[16] <- aux;
    return (h);
  }
  
  proc mulmod (h:W32.t Array17.t, r:W32.t Array17.t) : W32.t Array17.t = {
    var aux: int;
    var aux_0: W32.t;
    var aux_1: W32.t Array17.t;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    var i:int;
    var hr:W32.t Array17.t;
    hr <- witness;
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 17) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W32.of_int 0);
      u <- aux_0;
      leakages <- LeakFor(0,(i + 1)) :: LeakAddr([]) :: leakages;
      aux <- (i + 1);
      j <- 0;
      while (j < aux) {
        leakages <- LeakAddr([j]) :: leakages;
        aux_0 <- h.[j];
        tmp <- aux_0;
        leakages <- LeakAddr([(i - j)]) :: leakages;
        aux_0 <- (tmp * r.[(i - j)]);
        tmp <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (u + tmp);
        u <- aux_0;
        j <- j + 1;
      }
      leakages <- LeakFor((i + 1),17) :: LeakAddr([]) :: leakages;
      j <- (i + 1);
      while (j < 17) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (W32.of_int 320);
        tmp <- aux_0;
        leakages <- LeakAddr([j]) :: leakages;
        aux_0 <- (tmp * h.[j]);
        tmp <- aux_0;
        leakages <- LeakAddr([((i + 17) - j)]) :: leakages;
        aux_0 <- (tmp * r.[((i + 17) - j)]);
        tmp <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (u + tmp);
        u <- aux_0;
        j <- j + 1;
      }
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- u;
      leakages <- LeakAddr([i]) :: leakages;
      hr.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 17) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- hr.[i];
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- tmp;
      leakages <- LeakAddr([i]) :: leakages;
      h.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ squeeze (h);
    h <- aux_1;
    return (h);
  }
  
  proc poly1305 (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : W64.t = {
    var aux_7: bool;
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux: int;
    var aux_0: W8.t;
    var aux_1: W32.t;
    var aux_2: W64.t;
    var aux_8: W32.t Array17.t;
    
    var ret:W64.t;
    var i:int;
    var tmp:W8.t;
    var tmp32:W32.t;
    var r:W32.t Array17.t;
    var h:W32.t Array17.t;
    var one:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var eq:bool;
    var gt:bool;
    var c:W32.t Array17.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    c <- witness;
    h <- witness;
    r <- witness;
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 16) {
      leakages <- LeakAddr([(W64.to_uint (k + (W64.of_int i)))]) :: leakages;
      aux_0 <- (loadW8 Glob.mem (W64.to_uint (k + (W64.of_int i))));
      tmp <- aux_0;
      leakages <- LeakCond(((i %% 4) = 3)) :: LeakAddr([]) :: leakages;
      if (((i %% 4) = 3)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (tmp `&` (W8.of_int 15));
        tmp <- aux_0;
      } else {
        
      }
      leakages <- LeakCond((((i = 4) \/ (i = 8)) \/ (i = 12))) :: LeakAddr(
      []) :: leakages;
      if ((((i = 4) \/ (i = 8)) \/ (i = 12))) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (tmp `&` (W8.of_int 252));
        tmp <- aux_0;
      } else {
        
      }
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (zeroextu32 tmp);
      tmp32 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- tmp32;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W32.of_int 0);
    leakages <- LeakAddr([16]) :: leakages;
    r.[16] <- aux_1;
    leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 17) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W32.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      h.[i] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W32.of_int 1);
    one <- aux_1;
    
    leakages <- LeakCond(((W64.of_int 0) \ult inlen)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult inlen)) {
      leakages <- LeakCond(((W64.of_int 16) \ule inlen)) :: LeakAddr(
      []) :: leakages;
      if (((W64.of_int 16) \ule inlen)) {
        leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
        i <- 0;
        while (i < 16) {
          leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int i)))]) :: leakages;
          aux_0 <- (loadW8 Glob.mem (W64.to_uint (in_0 + (W64.of_int i))));
          tmp <- aux_0;
          leakages <- LeakAddr([]) :: leakages;
          aux_1 <- (zeroextu32 tmp);
          tmp32 <- aux_1;
          leakages <- LeakAddr([]) :: leakages;
          aux_1 <- tmp32;
          leakages <- LeakAddr([i]) :: leakages;
          c.[i] <- aux_1;
          i <- i + 1;
        }
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- one;
        leakages <- LeakAddr([16]) :: leakages;
        c.[16] <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_2 <- (in_0 + (W64.of_int 16));
        in_0 <- aux_2;
        leakages <- LeakAddr([]) :: leakages;
        aux_2 <- (inlen - (W64.of_int 16));
        inlen <- aux_2;
      } else {
        leakages <- LeakFor(0,17) :: LeakAddr([]) :: leakages;
        i <- 0;
        while (i < 17) {
          leakages <- LeakAddr([]) :: leakages;
          (aux_7, aux_6, aux_5, aux_4, aux_3, aux_1) <- set0_32 ;
          _of_ <- aux_7;
          _cf_ <- aux_6;
          _sf_ <- aux_5;
           _0 <- aux_4;
          _zf_ <- aux_3;
          tmp32 <- aux_1;
          leakages <- LeakAddr([]) :: leakages;
          (aux_7, aux_6, aux_5, aux_4, aux_3) <- CMP_64 inlen (W64.of_int i);
          _of_ <- aux_7;
          _cf_ <- aux_6;
          _sf_ <- aux_5;
           _1 <- aux_4;
          _zf_ <- aux_3;
          leakages <- LeakAddr([]) :: leakages;
          aux_7 <- (_EQ _of_ _cf_ _sf_ _zf_);
          eq <- aux_7;
          leakages <- LeakAddr([]) :: leakages;
          aux_7 <- (_sGT _of_ _cf_ _sf_ _zf_);
          gt <- aux_7;
          leakages <- LeakCond(gt) :: LeakAddr([]) :: leakages;
          if (gt) {
            leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int i)))]) :: leakages;
            aux_0 <- (loadW8 Glob.mem (W64.to_uint (in_0 + (W64.of_int i))));
            tmp <- aux_0;
            leakages <- LeakAddr([]) :: leakages;
            aux_1 <- (zeroextu32 tmp);
            tmp32 <- aux_1;
          } else {
            
          }
          leakages <- LeakAddr([]) :: leakages;
          aux_1 <- (eq ? one : tmp32);
          tmp32 <- aux_1;
          leakages <- LeakAddr([]) :: leakages;
          aux_1 <- tmp32;
          leakages <- LeakAddr([i]) :: leakages;
          c.[i] <- aux_1;
          i <- i + 1;
        }
        leakages <- LeakAddr([]) :: leakages;
        (aux_7, aux_6, aux_5, aux_4, aux_3, aux_2) <- set0_64 ;
        _of_ <- aux_7;
        _cf_ <- aux_6;
        _sf_ <- aux_5;
         _2 <- aux_4;
        _zf_ <- aux_3;
        inlen <- aux_2;
      }
      leakages <- LeakAddr([]) :: leakages;
      aux_8 <@ add (h, c);
      h <- aux_8;
      leakages <- LeakAddr([]) :: leakages;
      aux_8 <@ mulmod (h, r);
      h <- aux_8;
    leakages <- LeakCond(((W64.of_int 0) \ult inlen)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_8 <@ freeze (h);
    h <- aux_8;
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 16) {
      leakages <- LeakAddr([(W64.to_uint (k + (W64.of_int (i + 16))))]) :: leakages;
      aux_0 <- (loadW8 Glob.mem (W64.to_uint (k + (W64.of_int (i + 16)))));
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (zeroextu32 tmp);
      tmp32 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- tmp32;
      leakages <- LeakAddr([i]) :: leakages;
      c.[i] <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W32.of_int 0);
    leakages <- LeakAddr([16]) :: leakages;
    c.[16] <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    add_and_store (out, h, c);
    leakages <- LeakAddr([]) :: leakages;
    (aux_7, aux_6, aux_5, aux_4, aux_3, aux_2) <- set0_64 ;
    _of_ <- aux_7;
    _cf_ <- aux_6;
    _sf_ <- aux_5;
     _3 <- aux_4;
    _zf_ <- aux_3;
    ret <- aux_2;
    return (ret);
  }
}.

