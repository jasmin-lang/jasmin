require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array17.
require import WArray68.



module M = {
  proc add (h:W32.t Array17.t, c:W32.t Array17.t) : W32.t Array17.t = {
    var aux: int;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    u <- (W32.of_int 0);
    j <- 0;
    while (j < 17) {
      u <- (u + h.[j]);
      u <- (u + c.[j]);
      tmp <- u;
      tmp <- (tmp `&` (W32.of_int 255));
      h.[j] <- tmp;
      u <- (u `>>` (W8.of_int 8));
      j <- j + 1;
    }
    return (h);
  }
  
  proc add_minusp (h:W32.t Array17.t) : W32.t Array17.t = {
    var aux: int;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    u <- (W32.of_int 0);
    j <- 0;
    while (j < 17) {
      u <- (u + h.[j]);
      if ((j = 0)) {
        u <- (u + (W32.of_int 5));
      } else {
        
      }
      if ((j = 16)) {
        u <- (u + (W32.of_int 252));
      } else {
        
      }
      tmp <- u;
      tmp <- (tmp `&` (W32.of_int 255));
      h.[j] <- tmp;
      u <- (u `>>` (W8.of_int 8));
      j <- j + 1;
    }
    return (h);
  }
  
  proc add_and_store (out:W64.t, h:W32.t Array17.t, c:W32.t Array17.t) : unit = {
    var aux: int;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    u <- (W32.of_int 0);
    j <- 0;
    while (j < 16) {
      u <- (u + h.[j]);
      u <- (u + c.[j]);
      tmp <- u;
      tmp <- (tmp `&` (W32.of_int 255));
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + (W64.of_int j))) ((truncateu8 tmp));
      u <- (u `>>` (W8.of_int 8));
      j <- j + 1;
    }
    return ();
  }
  
  proc freeze (h:W32.t Array17.t) : W32.t Array17.t = {
    var aux: int;
    
    var j:int;
    var tmp:W32.t;
    var horig:W32.t Array17.t;
    var negative:W32.t;
    horig <- witness;
    j <- 0;
    while (j < 17) {
      tmp <- h.[j];
      horig.[j] <- tmp;
      j <- j + 1;
    }
    h <@ add_minusp (h);
    negative <- h.[16];
    negative <- (negative `>>` (W8.of_int 7));
    negative <- (- negative);
    j <- 0;
    while (j < 17) {
      tmp <- horig.[j];
      tmp <- (tmp `^` h.[j]);
      tmp <- (tmp `&` negative);
      h.[j] <- (h.[j] `^` tmp);
      j <- j + 1;
    }
    return (h);
  }
  
  proc squeeze (h:W32.t Array17.t) : W32.t Array17.t = {
    var aux: int;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    
    u <- (W32.of_int 0);
    j <- 0;
    while (j < 16) {
      u <- (u + h.[j]);
      tmp <- u;
      tmp <- (tmp `&` (W32.of_int 255));
      h.[j] <- tmp;
      u <- (u `>>` (W8.of_int 8));
      j <- j + 1;
    }
    u <- (u + h.[16]);
    tmp <- u;
    tmp <- (tmp `&` (W32.of_int 3));
    h.[16] <- tmp;
    u <- (u `>>` (W8.of_int 2));
    u <- (u * (W32.of_int 5));
    j <- 0;
    while (j < 16) {
      u <- (u + h.[j]);
      tmp <- u;
      tmp <- (tmp `&` (W32.of_int 255));
      h.[j] <- tmp;
      u <- (u `>>` (W8.of_int 8));
      j <- j + 1;
    }
    u <- (u + h.[16]);
    h.[16] <- u;
    return (h);
  }
  
  proc mulmod (h:W32.t Array17.t, r:W32.t Array17.t) : W32.t Array17.t = {
    var aux: int;
    
    var u:W32.t;
    var j:int;
    var tmp:W32.t;
    var i:int;
    var hr:W32.t Array17.t;
    hr <- witness;
    i <- 0;
    while (i < 17) {
      u <- (W32.of_int 0);
      aux <- (i + 1);
      j <- 0;
      while (j < aux) {
        tmp <- h.[j];
        tmp <- (tmp * r.[(i - j)]);
        u <- (u + tmp);
        j <- j + 1;
      }
      j <- (i + 1);
      while (j < 17) {
        tmp <- (W32.of_int 320);
        tmp <- (tmp * h.[j]);
        tmp <- (tmp * r.[((i + 17) - j)]);
        u <- (u + tmp);
        j <- j + 1;
      }
      hr.[i] <- u;
      i <- i + 1;
    }
    i <- 0;
    while (i < 17) {
      tmp <- hr.[i];
      h.[i] <- tmp;
      i <- i + 1;
    }
    h <@ squeeze (h);
    return (h);
  }
  
  proc poly1305 (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : W64.t = {
    var aux: int;
    
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
    i <- 0;
    while (i < 16) {
      tmp <- (loadW8 Glob.mem (W64.to_uint (k + (W64.of_int i))));
      if (((i %% 4) = 3)) {
        tmp <- (tmp `&` (W8.of_int 15));
      } else {
        
      }
      if ((((i = 4) \/ (i = 8)) \/ (i = 12))) {
        tmp <- (tmp `&` (W8.of_int 252));
      } else {
        
      }
      tmp32 <- (zeroextu32 tmp);
      r.[i] <- tmp32;
      i <- i + 1;
    }
    r.[16] <- (W32.of_int 0);
    i <- 0;
    while (i < 17) {
      h.[i] <- (W32.of_int 0);
      i <- i + 1;
    }
    one <- (W32.of_int 1);
    
    while (((W64.of_int 0) \ult inlen)) {
      if (((W64.of_int 16) \ule inlen)) {
        i <- 0;
        while (i < 16) {
          tmp <- (loadW8 Glob.mem (W64.to_uint (in_0 + (W64.of_int i))));
          tmp32 <- (zeroextu32 tmp);
          c.[i] <- tmp32;
          i <- i + 1;
        }
        c.[16] <- one;
        in_0 <- (in_0 + (W64.of_int 16));
        inlen <- (inlen - (W64.of_int 16));
      } else {
        i <- 0;
        while (i < 17) {
          (_of_, _cf_, _sf_,  _0, _zf_, tmp32) <- set0_32 ;
          (_of_, _cf_, _sf_,  _1, _zf_) <- CMP_64 inlen (W64.of_int i);
          eq <- (_EQ _of_ _cf_ _sf_ _zf_);
          gt <- (_sGT _of_ _cf_ _sf_ _zf_);
          if (gt) {
            tmp <- (loadW8 Glob.mem (W64.to_uint (in_0 + (W64.of_int i))));
            tmp32 <- (zeroextu32 tmp);
          } else {
            
          }
          tmp32 <- (eq ? one : tmp32);
          c.[i] <- tmp32;
          i <- i + 1;
        }
        (_of_, _cf_, _sf_,  _2, _zf_, inlen) <- set0_64 ;
      }
      h <@ add (h, c);
      h <@ mulmod (h, r);
    }
    h <@ freeze (h);
    i <- 0;
    while (i < 16) {
      tmp <- (loadW8 Glob.mem (W64.to_uint (k + (W64.of_int (i + 16)))));
      tmp32 <- (zeroextu32 tmp);
      c.[i] <- tmp32;
      i <- i + 1;
    }
    c.[16] <- (W32.of_int 0);
    add_and_store (out, h, c);
    (_of_, _cf_, _sf_,  _3, _zf_, ret) <- set0_64 ;
    return (ret);
  }
}.

