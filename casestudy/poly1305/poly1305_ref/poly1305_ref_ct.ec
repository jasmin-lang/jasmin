require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.

require import Array2 Array3.
require import WArray16 WArray24.


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
  
  proc poly1305_ref (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
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
}.
end T.

