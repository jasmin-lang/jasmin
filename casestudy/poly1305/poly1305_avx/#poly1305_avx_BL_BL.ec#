require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.

require import Array2 Array3 Array4 Array5.
require import WArray16 WArray24 WArray32 WArray40 WArray48 WArray64 WArray80.

abbrev bit25_u64 = W64.of_int 16777216.


abbrev mask26_u64 = W64.of_int 67108863.


abbrev five_u64 = W64.of_int 5.


abbrev zero_u64 = W64.of_int 0.

theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t
  
  proc load2 (p:W64.t) : W64.t Array2.t = {
    var aux: W64.t;
    
    var x:W64.t Array2.t;
    x <- witness;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 0))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 8))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))));
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    return (x);
  }
  
  proc load_add (h:W64.t Array3.t, in_0:W64.t) : W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    var  _0:bool;
    
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 0))))]
                         ++ [0]) :: leakages;
    (aux, aux_0) <- adc_64 h.[0]
    (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0)))) false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 8))))]
                         ++ [1]) :: leakages;
    (aux, aux_0) <- adc_64 h.[1]
    (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int 8)))) cf;
    cf <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux, aux_0) <- adc_64 h.[2] (W64.of_int 1) cf;
     _0 <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    return (h);
  }
  
  proc load_last_add (h:W64.t Array3.t, in_0:W64.t, len:W64.t) : W64.t Array3.t = {
    var aux_1: bool;
    var aux_0: W8.t;
    var aux: W64.t;
    
    var s:W64.t Array2.t;
    var j:W64.t;
    var c:W8.t;
    var cf:bool;
    var  _0:bool;
    s <- witness;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    aux <- (W64.of_int 0);
    j <- aux;
    
    leakages <- LeakCond((j \ult len)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult len)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + j)))]) :: leakages;
      aux_0 <- (loadW8 Glob.mem (W64.to_uint (in_0 + j)));
      c <- aux_0;
      aux_0 <- c;
      leakages <- LeakAddr([(W64.to_uint j)]) :: leakages;
      s <-
      Array2.init
      (WArray16.get64 (WArray16.set8 (WArray16.init64 (fun i => s.[i])) (W64.to_uint j) aux_0));
      aux <- (j + (W64.of_int 1));
      j <- aux;
    leakages <- LeakCond((j \ult len)) :: LeakAddr([]) :: leakages;
    
    }
    aux_0 <- (W8.of_int 1);
    leakages <- LeakAddr([(W64.to_uint j)]) :: leakages;
    s <-
    Array2.init
    (WArray16.get64 (WArray16.set8 (WArray16.init64 (fun i => s.[i])) (W64.to_uint j) aux_0));
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    (aux_1, aux) <- adc_64 h.[0] s.[0] false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    (aux_1, aux) <- adc_64 h.[1] s.[1] cf;
    cf <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux) <- adc_64 h.[2] (W64.of_int 0) cf;
     _0 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    return (h);
  }
  
  proc store2 (p:W64.t, x:W64.t Array2.t) : unit = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 0))))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- x.[1];
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 8))))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) aux;
    return ();
  }
  
  proc clamp (k:W64.t) : W64.t Array3.t = {
    var aux: W64.t;
    
    var r:W64.t Array3.t;
    r <- witness;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (k + (W64.of_int 0))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (k + (W64.of_int 0))));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (k + (W64.of_int 8))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (k + (W64.of_int 8))));
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r.[0] `&` (W64.of_int 1152921487695413247));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (r.[1] `&` (W64.of_int 1152921487695413244));
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- r.[1];
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (r.[2] `>>` (W8.of_int 2));
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux;
    leakages <- LeakAddr([1] ++ [2]) :: leakages;
    aux <- (r.[2] + r.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux;
    return (r);
  }
  
  proc add2 (h:W64.t Array2.t, s:W64.t Array2.t) : W64.t Array2.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var cf:bool;
    var  _0:bool;
    
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    (aux, aux_0) <- adc_64 h.[0] s.[0] false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    (aux, aux_0) <- adc_64 h.[1] s.[1] cf;
     _0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    return (h);
  }
  
  proc mulmod (h:W64.t Array3.t, r:W64.t Array3.t) : W64.t Array3.t = {
    var aux_1: bool;
    var aux_0: W64.t;
    var aux: W64.t;
    
    var t2:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var t0:W64.t;
    var t1:W64.t;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- r.[2];
    t2 <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (t2 * h.[2]);
    t2 <- aux_0;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux_0 <- (h.[2] * r.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r.[0];
    rax <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[0];
    rdx <- aux_0;
    rax <- aux;
    aux_0 <- rax;
    t0 <- aux_0;
    aux_0 <- rdx;
    t1 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r.[0];
    rax <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[1];
    rdx <- aux_0;
    rax <- aux;
    (aux_1, aux_0) <- adc_64 t1 rax false;
    cf <- aux_1;
    t1 <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[2] rdx cf;
     _0 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- r.[2];
    rax <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[1];
    rdx <- aux_0;
    rax <- aux;
    aux_0 <- rdx;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- (h.[1] + t2);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    aux_0 <- rax;
    t2 <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- r.[1];
    rax <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[0];
    rdx <- aux_0;
    rax <- aux;
    (aux_1, aux_0) <- adc_64 t0 t2 false;
    cf <- aux_1;
    t0 <- aux_0;
    (aux_1, aux_0) <- adc_64 t1 rax cf;
    cf <- aux_1;
    t1 <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[2] rdx cf;
     _1 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    aux_0 <- (W64.of_int 18446744073709551612);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- h.[2];
    t2 <- aux_0;
    aux_0 <- (t2 `>>` (W8.of_int 2));
    t2 <- aux_0;
    leakages <- LeakAddr([2] ++ [0]) :: leakages;
    aux_0 <- (h.[0] `&` h.[2]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (h.[0] + t2);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (h.[2] `&` (W64.of_int 3));
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[0] t0 false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[1] t1 cf;
    cf <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[2] (W64.of_int 0) cf;
     _2 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    return (h);
  }
  
  proc freeze (h:W64.t Array3.t) : W64.t Array2.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var g:W64.t Array2.t;
    var g2:W64.t;
    var cf:bool;
    var mask:W64.t;
    var  _0:bool;
    g <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- h.[0];
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- h.[1];
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- h.[2];
    g2 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- adc_64 g.[0] (W64.of_int 5) false;
    cf <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_0, aux) <- adc_64 g.[1] (W64.of_int 0) cf;
    cf <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    (aux_0, aux) <- adc_64 g2 (W64.of_int 0) cf;
     _0 <- aux_0;
    g2 <- aux;
    aux <- (g2 `>>` (W8.of_int 2));
    g2 <- aux;
    aux <- (- g2);
    mask <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (g.[0] `^` h.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (g.[1] `^` h.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (g.[0] `&` mask);
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (g.[1] `&` mask);
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (g.[0] `^` h.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (g.[1] `^` h.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    return (g);
  }
  
  proc poly1305_ref3_setup (k:W64.t) : W64.t Array3.t * W64.t Array3.t *
                                       W64.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array3.t;
    
    var h:W64.t Array3.t;
    var r:W64.t Array3.t;
    var i:int;
    h <- witness;
    r <- witness;
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 3) {
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      h.[i] <- aux_0;
      i <- i + 1;
    }
    aux_1 <@ clamp (k);
    r <- aux_1;
    aux_0 <- (k + (W64.of_int 16));
    k <- aux_0;
    return (h, r, k);
  }
  
  proc poly1305_ref3_update (in_0:W64.t, inlen:W64.t, h:W64.t Array3.t,
                             r:W64.t Array3.t) : W64.t * W64.t *
                                                 W64.t Array3.t = {
    var aux_0: W64.t;
    var aux: W64.t Array3.t;
    
    
    
    
    leakages <- LeakCond(((W64.of_int 16) \ule inlen)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 16) \ule inlen)) {
      aux <@ load_add (h, in_0);
      h <- aux;
      aux <@ mulmod (h, r);
      h <- aux;
      aux_0 <- (in_0 + (W64.of_int 16));
      in_0 <- aux_0;
      aux_0 <- (inlen - (W64.of_int 16));
      inlen <- aux_0;
    leakages <- LeakCond(((W64.of_int 16) \ule inlen)) :: LeakAddr([]) :: leakages;
    
    }
    return (in_0, inlen, h);
  }
  
  proc poly1305_ref3_last (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t,
                           h:W64.t Array3.t, r:W64.t Array3.t) : unit = {
    var aux_0: W64.t Array2.t;
    var aux: W64.t Array3.t;
    
    var h2:W64.t Array2.t;
    var s:W64.t Array2.t;
    h2 <- witness;
    s <- witness;
    leakages <- LeakCond(((W64.of_int 0) \ult inlen)) :: LeakAddr([]) :: leakages;
    if (((W64.of_int 0) \ult inlen)) {
      aux <@ load_last_add (h, in_0, inlen);
      h <- aux;
      aux <@ mulmod (h, r);
      h <- aux;
    } else {
      
    }
    aux_0 <@ freeze (h);
    h2 <- aux_0;
    aux_0 <@ load2 (k);
    s <- aux_0;
    aux_0 <@ add2 (h2, s);
    h2 <- aux_0;
    store2 (out, h2);
    return ();
  }
  
  proc poly1305_ref3_local (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux_0: W64.t Array3.t;
    var aux: W64.t Array3.t;
    
    var h:W64.t Array3.t;
    var r:W64.t Array3.t;
    var len:W64.t;
    h <- witness;
    r <- witness;
    (aux_0, aux, aux_2) <@ poly1305_ref3_setup (k);
    h <- aux_0;
    r <- aux;
    k <- aux_2;
    aux_2 <- inlen;
    len <- aux_2;
    (aux_2, aux_1, aux_0) <@ poly1305_ref3_update (in_0, len, h, r);
    in_0 <- aux_2;
    len <- aux_1;
    h <- aux_0;
    poly1305_ref3_last (out, in_0, len, k, h, r);
    return ();
  }
  
  proc times_5 (r12:W128.t Array5.t) : W128.t Array4.t = {
    var aux_0: int;
    var aux: W128.t;
    
    var r12x5:W128.t Array4.t;
    var five:W128.t;
    var i:int;
    var t:W128.t;
    r12x5 <- witness;
    aux <- VPBROADCAST_2u64 five_u64;
    five <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([(1 + i)]) :: leakages;
      aux <- VPMULU_128 five r12.[(1 + i)];
      t <- aux;
      aux <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r12x5.[i] <- aux;
      i <- i + 1;
    }
    return (r12x5);
  }
  
  proc broadcast_r2 (r12:W128.t Array5.t, r12x5:W128.t Array4.t) : W128.t Array5.t *
                                                                   W128.t Array4.t = {
    var aux: int;
    var aux_0: W128.t;
    
    var r22:W128.t Array5.t;
    var r22x5:W128.t Array4.t;
    var i:int;
    var t:W128.t Array5.t;
    r22 <- witness;
    r22x5 <- witness;
    t <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([(2 * i)]) :: leakages;
      aux_0 <- VPBROADCAST_2u64 (get64 (WArray80.init128 (fun i => r12.[i]))
                                (2 * i));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- t.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r22.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([(2 * i)]) :: leakages;
      aux_0 <- VPBROADCAST_2u64 (get64
                                (WArray64.init128 (fun i => r12x5.[i]))
                                (2 * i));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- t.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r22x5.[i] <- aux_0;
      i <- i + 1;
    }
    return (r22, r22x5);
  }
  
  proc broadcast_r4 (r4:W64.t Array3.t) : W128.t Array5.t * W128.t Array4.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    var aux_6: W128.t Array4.t;
    
    var r44:W128.t Array5.t;
    var r44x5:W128.t Array4.t;
    var mask26:int;
    var l:W64.t;
    var h:W64.t;
    var i:int;
    var t:W64.t Array5.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    r44 <- witness;
    r44x5 <- witness;
    t <- witness;
    aux <- 67108863;
    mask26 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r4.[0];
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 0)]) :: leakages;
    r44 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r44.[i])) (0 + 0) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r4.[0];
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 2)]) :: leakages;
    r44 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r44.[i])) (0 + 2) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r4.[0];
    l <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l r4.[1]
    (W8.of_int 52);
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
     _4 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    h <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 4)]) :: leakages;
    r44 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r44.[i])) (0 + 4) aux_0));
    aux_0 <- h;
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 6)]) :: leakages;
    r44 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r44.[i])) (0 + 6) aux_0));
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- r4.[1];
    l <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l r4.[2]
    (W8.of_int 40);
     _5 <- aux_5;
     _6 <- aux_4;
     _7 <- aux_3;
     _8 <- aux_2;
     _9 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 8)]) :: leakages;
    r44 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r44.[i])) (0 + 8) aux_0));
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([(2 * i)]) :: leakages;
      aux_0 <- (get64 (WArray80.init128 (fun i => r44.[i])) (2 * i));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- t.[i];
      leakages <- LeakAddr([(1 + (2 * i))]) :: leakages;
      r44 <-
      Array5.init
      (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r44.[i])) (1 + (2 * i)) aux_0));
      i <- i + 1;
    }
    aux_6 <@ times_5 (r44);
    r44x5 <- aux_6;
    return (r44, r44x5);
  }
  
  proc poly1305_avx_setup (r:W64.t Array3.t) : W128.t Array5.t *
                                               W128.t Array4.t *
                                               W128.t Array5.t *
                                               W128.t Array4.t *
                                               W128.t Array5.t *
                                               W128.t Array4.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    var aux_6: W64.t Array3.t;
    var aux_7: W128.t Array4.t;
    var aux_8: W128.t Array5.t;
    
    var r44:W128.t Array5.t;
    var r44x5:W128.t Array4.t;
    var r22:W128.t Array5.t;
    var r22x5:W128.t Array4.t;
    var r12:W128.t Array5.t;
    var r12x5:W128.t Array4.t;
    var i:int;
    var rt:W64.t Array3.t;
    var mask26:int;
    var l:W64.t;
    var h:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    r12 <- witness;
    r12x5 <- witness;
    r22 <- witness;
    r22x5 <- witness;
    r44 <- witness;
    r44x5 <- witness;
    rt <- witness;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- r.[i];
      leakages <- LeakAddr([i]) :: leakages;
      rt.[i] <- aux_0;
      i <- i + 1;
    }
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    rt.[2] <- aux_0;
    aux <- 67108863;
    mask26 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(1 + 0)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (1 + 0) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(1 + 2)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (1 + 2) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[1]
    (W8.of_int 52);
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
     _4 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    h <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(1 + 4)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (1 + 4) aux_0));
    aux_0 <- h;
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(1 + 6)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (1 + 6) aux_0));
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- rt.[1];
    l <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[2]
    (W8.of_int 40);
     _5 <- aux_5;
     _6 <- aux_4;
     _7 <- aux_3;
     _8 <- aux_2;
     _9 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(1 + 8)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (1 + 8) aux_0));
    aux_6 <@ mulmod (rt, r);
    rt <- aux_6;
    aux <- 67108863;
    mask26 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 0)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (0 + 0) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 2)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (0 + 2) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[1]
    (W8.of_int 52);
     _10 <- aux_5;
     _11 <- aux_4;
     _12 <- aux_3;
     _13 <- aux_2;
     _14 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    h <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 4)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (0 + 4) aux_0));
    aux_0 <- h;
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 6)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (0 + 6) aux_0));
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- rt.[1];
    l <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[2]
    (W8.of_int 40);
     _15 <- aux_5;
     _16 <- aux_4;
     _17 <- aux_3;
     _18 <- aux_2;
     _19 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(0 + 8)]) :: leakages;
    r12 <-
    Array5.init
    (WArray80.get128 (WArray80.set64 (WArray80.init128 (fun i => r12.[i])) (0 + 8) aux_0));
    aux_7 <@ times_5 (r12);
    r12x5 <- aux_7;
    (aux_8, aux_7) <@ broadcast_r2 (r12, r12x5);
    r22 <- aux_8;
    r22x5 <- aux_7;
    aux_6 <@ mulmod (rt, r);
    rt <- aux_6;
    aux_6 <@ mulmod (rt, r);
    rt <- aux_6;
    (aux_8, aux_7) <@ broadcast_r4 (rt);
    r44 <- aux_8;
    r44x5 <- aux_7;
    return (r44, r44x5, r22, r22x5, r12, r12x5);
  }
  
  proc pack_avx (h:W128.t Array5.t) : W64.t Array3.t = {
    var aux_1: bool;
    var aux_0: W64.t;
    var aux: W128.t;
    
    var r:W64.t Array3.t;
    var t:W128.t Array3.t;
    var u:W128.t Array2.t;
    var d:W64.t Array3.t;
    var cf:bool;
    var c:W64.t;
    var cx4:W64.t;
    var  _0:bool;
    var  _1:bool;
    d <- witness;
    r <- witness;
    t <- witness;
    u <- witness;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (h.[1] \vshl64u128 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 h.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (h.[3] \vshl64u128 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 h.[2]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPSRLDQ_128 h.[4] (W8.of_int 8);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([4] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 h.[4]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPUNPCKL_2u64 t.[0] t.[1];
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPUNPCKH_2u64 t.[0] t.[1];
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- (u.[0] \vadd64u128 u.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- VPEXTR_64 t.[0] (W8.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    d.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- VPEXTR_64 t.[0] (W8.of_int 1);
    leakages <- LeakAddr([1]) :: leakages;
    d.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- VPEXTR_64 t.[2] (W8.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    d.[2] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- d.[1];
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (r.[0] `<<` (W8.of_int 52));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- d.[1];
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- (r.[1] `>>` (W8.of_int 12));
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- d.[2];
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (r.[2] `>>` (W8.of_int 24));
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (d.[2] `<<` (W8.of_int 40));
    leakages <- LeakAddr([2]) :: leakages;
    d.[2] <- aux_0;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    (aux_1, aux_0) <- adc_64 r.[0] d.[0] false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakAddr([2] ++ [1]) :: leakages;
    (aux_1, aux_0) <- adc_64 r.[1] d.[2] cf;
    cf <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 r.[2] (W64.of_int 0) cf;
     _0 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- r.[2];
    c <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- r.[2];
    cx4 <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (r.[2] `&` (W64.of_int 3));
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_0;
    aux_0 <- (c `>>` (W8.of_int 2));
    c <- aux_0;
    aux_0 <- (cx4 `&` (W64.of_int (- 4)));
    cx4 <- aux_0;
    aux_0 <- (c + cx4);
    c <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_1, aux_0) <- adc_64 r.[0] c false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_1, aux_0) <- adc_64 r.[1] (W64.of_int 0) cf;
    cf <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 r.[2] (W64.of_int 0) cf;
     _1 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_0;
    return (r);
  }
  
  proc carry_reduce_avx (x:W128.t Array5.t, mask26:W128.t) : W128.t Array5.t = {
    var aux: W128.t;
    
    var z:W128.t Array2.t;
    var t:W128.t;
    z <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (x.[1] \vadd64u128 z.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (x.[4] \vadd64u128 z.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    x.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (x.[1] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (x.[4] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (z.[1] \vshl64u128 (W8.of_int 2));
    t <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (z.[1] \vadd64u128 t);
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (x.[1] `&` mask26);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (x.[4] `&` mask26);
    leakages <- LeakAddr([4]) :: leakages;
    x.[4] <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (x.[2] \vadd64u128 z.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- (x.[0] \vadd64u128 z.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (x.[2] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (x.[2] `&` mask26);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (x.[3] \vadd64u128 z.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (x.[1] \vadd64u128 z.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux;
    leakages <- LeakAddr([0] ++ [4]) :: leakages;
    aux <- (x.[4] \vadd64u128 z.[0]);
    leakages <- LeakAddr([4]) :: leakages;
    x.[4] <- aux;
    return (x);
  }
  
  proc mulmod_avx (h:W128.t Array5.t, s_r:W128.t Array5.t,
                   s_rx5:W128.t Array4.t, s_mask26:W128.t, s_bit25:W128.t) : 
  W128.t Array5.t = {
    var aux: W128.t;
    
    var r0:W128.t;
    var r1:W128.t;
    var r4x5:W128.t;
    var t:W128.t Array5.t;
    var u:W128.t Array4.t;
    var r2:W128.t;
    var r3x5:W128.t;
    var r3:W128.t;
    var r2x5:W128.t;
    t <- witness;
    u <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s_r.[0];
    r0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- s_r.[1];
    r1 <- aux;
    leakages <- LeakAddr([(4 - 1)]) :: leakages;
    aux <- s_rx5.[(4 - 1)];
    r4x5 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r0;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r0;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r0;
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r0;
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r0;
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r1;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r1;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r1;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r1;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- s_r.[2];
    r2 <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([1] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([2] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[2]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([3] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[3]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r4x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r4x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r4x5;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r4x5;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([(3 - 1)]) :: leakages;
    aux <- s_rx5.[(3 - 1)];
    r3x5 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r2;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r2;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r2;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- s_r.[3];
    r3 <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([1] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[1]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([2] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[2]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r3x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r3x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r3x5;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([(2 - 1)]) :: leakages;
    aux <- s_rx5.[(2 - 1)];
    r2x5 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u128 t.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r3;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r3;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r2x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r2x5;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u128 t.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([(1 - 1)] ++ [4]) :: leakages;
    aux <- VPMULU_128 h.[4] s_rx5.[(1 - 1)];
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([4] ++ [0]) :: leakages;
    aux <- VPMULU_128 h.[0] s_r.[4];
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- t.[3];
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    return (h);
  }
  
  proc mainloop_avx_v1 (h:W128.t Array5.t, in_0:W64.t, s_r44:W128.t Array5.t,
                        s_r44x5:W128.t Array4.t, s_r22:W128.t Array5.t,
                        s_r22x5:W128.t Array4.t, s_mask26:W128.t,
                        s_bit25:W128.t) : W128.t Array5.t * W64.t = {
    var aux_0: W64.t;
    var aux: W128.t;
    var aux_1: W128.t Array5.t;
    
    var r0:W128.t;
    var r1:W128.t;
    var r4x5:W128.t;
    var t:W128.t Array5.t;
    var u:W128.t Array4.t;
    var m0:W128.t;
    var r2:W128.t;
    var m1:W128.t;
    var m:W128.t Array5.t;
    var r3x5:W128.t;
    var r3:W128.t;
    var s_h:W128.t Array5.t;
    var r2x5:W128.t;
    var mt:W128.t;
    var mask26:W128.t;
    m <- witness;
    s_h <- witness;
    t <- witness;
    u <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s_r44.[0];
    r0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- s_r44.[1];
    r1 <- aux;
    leakages <- LeakAddr([(4 - 1)]) :: leakages;
    aux <- s_r44x5.[(4 - 1)];
    r4x5 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r0;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r1;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r0;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r1;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r0;
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r1;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r0;
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r1;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([1] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r0;
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([2] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[2]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([3] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[3]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r4x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 0))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    m0 <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r4x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- s_r44.[2];
    r2 <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r4x5;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r4x5;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 16))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 16))));
    m1 <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r2;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    aux <- VPUNPCKL_2u64 m0 m1;
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r2;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    aux <- VPUNPCKH_2u64 m0 m1;
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r2;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([(3 - 1)]) :: leakages;
    aux <- s_r44x5.[(3 - 1)];
    r3x5 <- aux;
    leakages <- LeakAddr([1] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[1]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([2] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[2]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 h.[2] r3x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r3x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- m.[0];
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r3x5;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (m.[1] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (m.[1] `&` s_mask26);
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- s_r44.[3];
    r3 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u128 t.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 h.[0] r3;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- m.[3];
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- h.[2];
    leakages <- LeakAddr([2]) :: leakages;
    s_h.[2] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 h.[1] r3;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (m.[4] \vshr64u128 (W8.of_int 40));
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (m.[4] `|` s_bit25);
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([(2 - 1)]) :: leakages;
    aux <- s_r44x5.[(2 - 1)];
    r2x5 <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 h.[3] r2x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- m.[0];
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- t.[3];
    leakages <- LeakAddr([3]) :: leakages;
    s_h.[3] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 h.[4] r2x5;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (m.[2] \vshr64u128 (W8.of_int 52));
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u128 t.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([(1 - 1)] ++ [4]) :: leakages;
    aux <- VPMULU_128 h.[4] s_r44x5.[(1 - 1)];
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] \vshl64u128 (W8.of_int 12));
    mt <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- h.[1];
    leakages <- LeakAddr([1]) :: leakages;
    s_h.[1] <- aux;
    leakages <- LeakAddr([4] ++ [0]) :: leakages;
    aux <- VPMULU_128 h.[0] s_r44.[4];
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (m.[2] `|` mt);
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    aux <- s_mask26;
    mask26 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- h.[0];
    leakages <- LeakAddr([0]) :: leakages;
    s_h.[0] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- h.[4];
    leakages <- LeakAddr([4]) :: leakages;
    s_h.[4] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (m.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (m.[2] `&` mask26);
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] \vshr64u128 (W8.of_int 14));
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s_r22.[0];
    r0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- s_r22.[1];
    r1 <- aux;
    leakages <- LeakAddr([(4 - 1)]) :: leakages;
    aux <- s_r22x5.[(4 - 1)];
    r4x5 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 m.[0] r0;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 m.[0] r1;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 m.[1] r0;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 m.[1] r1;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 m.[2] r0;
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 m.[2] r1;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 s_h.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 m.[3] r0;
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 s_h.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 m.[3] r1;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 s_h.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([1] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 m.[4] r0;
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 s_h.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([2] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[2]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([4] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 s_h.[4]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([3] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[3]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 m.[1] r4x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 32))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 32))));
    m0 <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 m.[2] r4x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- s_r22.[2];
    r2 <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 m.[3] r4x5;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 m.[4] r4x5;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 48))))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (in_0 + (W64.of_int 48))));
    m1 <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 m.[0] r2;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    aux <- VPUNPCKL_2u64 m0 m1;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 m.[1] r2;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    aux <- VPUNPCKH_2u64 m0 m1;
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 m.[2] r2;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u128 u.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([(3 - 1)]) :: leakages;
    aux <- s_r22x5.[(3 - 1)];
    r3x5 <- aux;
    leakages <- LeakAddr([1] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[1]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([2] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[2]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_128 m.[2] r3x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 m.[3] r3x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- h.[0];
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 m.[4] r3x5;
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (h.[1] \vshr64u128 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (h.[1] `&` s_mask26);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- s_r22.[3];
    r3 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u128 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (m.[2] \vadd64u128 t.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_128 m.[0] r3;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- h.[3];
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_128 m.[1] r3;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (h.[4] \vshr64u128 (W8.of_int 40));
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (h.[4] `|` s_bit25);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([(2 - 1)]) :: leakages;
    aux <- s_r22x5.[(2 - 1)];
    r2x5 <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u128 u.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_128 m.[3] r2x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- h.[0];
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_128 m.[4] r2x5;
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (h.[2] \vshr64u128 (W8.of_int 52));
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (m.[1] \vadd64u128 t.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([(1 - 1)] ++ [4]) :: leakages;
    aux <- VPMULU_128 m.[4] s_r22x5.[(1 - 1)];
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (h.[3] \vshl64u128 (W8.of_int 12));
    mt <- aux;
    leakages <- LeakAddr([4] ++ [0]) :: leakages;
    aux <- VPMULU_128 m.[0] s_r22.[4];
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (h.[2] `|` mt);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    aux <- s_mask26;
    mask26 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u128 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- t.[3];
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u128 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (h.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (h.[0] \vadd64u128 m.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (h.[2] `&` mask26);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u128 m.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (h.[3] \vshr64u128 (W8.of_int 14));
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (h.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (h.[3] \vadd64u128 m.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    aux_0 <- (in_0 + (W64.of_int 64));
    in_0 <- aux_0;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u128 m.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([4] ++ [4]) :: leakages;
    aux <- (h.[4] \vadd64u128 m.[4]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    aux_1 <@ carry_reduce_avx (h, mask26);
    h <- aux_1;
    return (h, in_0);
  }
  
  proc final_avx_v0 (h:W128.t Array5.t, s_r:W128.t Array5.t,
                     s_rx5:W128.t Array4.t, s_mask26:W128.t, s_bit25:W128.t) : 
  W128.t Array5.t = {
    var aux_0: W128.t;
    var aux: W128.t Array5.t;
    
    var mask26:W128.t;
    
    aux <@ mulmod_avx (h, s_r, s_rx5, s_mask26, s_bit25);
    h <- aux;
    aux_0 <- s_mask26;
    mask26 <- aux_0;
    aux <@ carry_reduce_avx (h, mask26);
    h <- aux;
    return (h);
  }
  
  proc poly1305_avx_update (in_0:W64.t, len:W64.t, r44:W128.t Array5.t,
                            r44x5:W128.t Array4.t, r22:W128.t Array5.t,
                            r22x5:W128.t Array4.t, r12:W128.t Array5.t,
                            r12x5:W128.t Array4.t) : W64.t * W64.t *
                                                     W64.t Array3.t = {
    var aux: int;
    var aux_2: W64.t;
    var aux_0: W128.t;
    var aux_3: W64.t Array3.t;
    var aux_1: W128.t Array5.t;
    
    var h64:W64.t Array3.t;
    var i:int;
    var h:W128.t Array5.t;
    var t:W128.t;
    var s_mask26:W128.t;
    var mask26:W128.t;
    var s_bit25:W128.t;
    h <- witness;
    h64 <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      aux_0 <- VPBROADCAST_2u64 zero_u64;
      leakages <- LeakAddr([i]) :: leakages;
      h.[i] <- aux_0;
      i <- i + 1;
    }
    aux_0 <- VPBROADCAST_2u64 mask26_u64;
    t <- aux_0;
    aux_0 <- t;
    s_mask26 <- aux_0;
    aux_0 <- t;
    mask26 <- aux_0;
    aux_0 <- VPBROADCAST_2u64 bit25_u64;
    t <- aux_0;
    aux_0 <- t;
    s_bit25 <- aux_0;
    
    leakages <- LeakCond(((W64.of_int 64) \ule len)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 64) \ule len)) {
      (aux_1, aux_2) <@ mainloop_avx_v1 (h, in_0, r44, r44x5, r22, r22x5,
      s_mask26, s_bit25);
      h <- aux_1;
      in_0 <- aux_2;
      aux_2 <- (len - (W64.of_int 64));
      len <- aux_2;
    leakages <- LeakCond(((W64.of_int 64) \ule len)) :: LeakAddr([]) :: leakages;
    
    }
    aux_1 <@ final_avx_v0 (h, r12, r12x5, s_mask26, s_bit25);
    h <- aux_1;
    aux_3 <@ pack_avx (h);
    h64 <- aux_3;
    return (in_0, len, h64);
  }
  
  proc poly1305_avx_wrapper (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    var aux_8: W64.t;
    var aux: W64.t;
    var aux_1: W64.t Array3.t;
    var aux_0: W64.t Array3.t;
    var aux_7: W128.t Array4.t;
    var aux_5: W128.t Array4.t;
    var aux_3: W128.t Array4.t;
    var aux_6: W128.t Array5.t;
    var aux_4: W128.t Array5.t;
    var aux_2: W128.t Array5.t;
    
    var len:W64.t;
    var h:W64.t Array3.t;
    var r:W64.t Array3.t;
    var r44:W128.t Array5.t;
    var r44x5:W128.t Array4.t;
    var r22:W128.t Array5.t;
    var r22x5:W128.t Array4.t;
    var r12:W128.t Array5.t;
    var r12x5:W128.t Array4.t;
    h <- witness;
    r <- witness;
    r12 <- witness;
    r12x5 <- witness;
    r22 <- witness;
    r22x5 <- witness;
    r44 <- witness;
    r44x5 <- witness;
    aux_8 <- inlen;
    len <- aux_8;
    (aux_1, aux_0, aux_8) <@ poly1305_ref3_setup (k);
    h <- aux_1;
    r <- aux_0;
    k <- aux_8;
    (aux_6, aux_7, aux_4, aux_5, aux_2, aux_3) <@ poly1305_avx_setup (r);
    r44 <- aux_6;
    r44x5 <- aux_7;
    r22 <- aux_4;
    r22x5 <- aux_5;
    r12 <- aux_2;
    r12x5 <- aux_3;
    (aux_8, aux, aux_1) <@ poly1305_avx_update (in_0, len, r44, r44x5, r22,
    r22x5, r12, r12x5);
    in_0 <- aux_8;
    len <- aux;
    h <- aux_1;
    (aux_8, aux, aux_1) <@ poly1305_ref3_update (in_0, len, h, r);
    in_0 <- aux_8;
    len <- aux;
    h <- aux_1;
    poly1305_ref3_last (out, in_0, len, k, h, r);
    return ();
  }
  
  proc poly1305_avx (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    
    
    
    leakages <- LeakCond((inlen \ult (W64.of_int 1024))) :: LeakAddr(
    []) :: leakages;
    if ((inlen \ult (W64.of_int 1024))) {
      poly1305_ref3_local (out, in_0, inlen, k);
    } else {
      poly1305_avx_wrapper (out, in_0, inlen, k);
    }
    return ();
  }
}.
end T.

