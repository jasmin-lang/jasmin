require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.

require import Array5 Array25.
require import WArray40 WArray200.


theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t
  
  proc index (x:int, y:int) : int = {
    var aux: int;
    
    var r:int;
    
    aux <- ((5 * (x %% 5)) + (y %% 5));
    r <- aux;
    return (r);
  }
  
  proc keccak_rho_offsets (i:int) : int = {
    var aux: int;
    
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    
    aux <- 0;
    r <- aux;
    aux <- 1;
    x <- aux;
    aux <- 0;
    y <- aux;
    leakages <- LeakFor(0,24) :: LeakAddr([]) :: leakages;
    t <- 0;
    while (t < 24) {
      leakages <- LeakCond((i = (x + (5 * y)))) :: LeakAddr([]) :: leakages;
      if ((i = (x + (5 * y)))) {
        aux <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
        r <- aux;
      } else {
        
      }
      aux <- (((2 * x) + (3 * y)) %% 5);
      z <- aux;
      aux <- y;
      x <- aux;
      aux <- z;
      y <- aux;
      t <- t + 1;
    }
    return (r);
  }
  
  proc rhotates (x:int, y:int) : int = {
    var aux: int;
    
    var r:int;
    var i:int;
    
    aux <@ index (x, y);
    i <- aux;
    aux <@ keccak_rho_offsets (i);
    r <- aux;
    return (r);
  }
  
  proc rOL64 (x:W64.t, c:int) : W64.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux: W64.t;
    
    var y:W64.t;
    var  _0:bool;
    var  _1:bool;
    
    leakages <- LeakCond((c = 0)) :: LeakAddr([]) :: leakages;
    if ((c = 0)) {
      aux <- x;
      y <- aux;
    } else {
      (aux_1, aux_0, aux) <- ROL_64 x (W8.of_int c);
       _0 <- aux_1;
       _1 <- aux_0;
      y <- aux;
    }
    return (y);
  }
  
  proc theta_sum (a:W64.t Array25.t) : W64.t Array5.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var c:W64.t Array5.t;
    var i:int;
    var j:int;
    c <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([((5 * (0 %% 5)) + (i %% 5))]) :: leakages;
      aux_0 <- a.[((5 * (0 %% 5)) + (i %% 5))];
      leakages <- LeakAddr([i]) :: leakages;
      c.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(1,5) :: LeakAddr([]) :: leakages;
    j <- 1;
    while (j < 5) {
      leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
      i <- 0;
      while (i < 5) {
        leakages <- LeakAddr([((5 * (j %% 5)) + (i %% 5))] ++ [i]) :: leakages;
        aux_0 <- (c.[i] `^` a.[((5 * (j %% 5)) + (i %% 5))]);
        leakages <- LeakAddr([i]) :: leakages;
        c.[i] <- aux_0;
        i <- i + 1;
      }
      j <- j + 1;
    }
    return (c);
  }
  
  proc theta_rol (c:W64.t Array5.t) : W64.t Array5.t = {
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var d:W64.t Array5.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    d <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([((i + 1) %% 5)]) :: leakages;
      aux_0 <- c.[((i + 1) %% 5)];
      leakages <- LeakAddr([i]) :: leakages;
      d.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_2, aux_1, aux_0) <- ROL_64 d.[i] (W8.of_int 1);
       _0 <- aux_2;
       _1 <- aux_1;
      leakages <- LeakAddr([i]) :: leakages;
      d.[i] <- aux_0;
      leakages <- LeakAddr([((i + 4) %% 5)] ++ [i]) :: leakages;
      aux_0 <- (d.[i] `^` c.[((i + 4) %% 5)]);
      leakages <- LeakAddr([i]) :: leakages;
      d.[i] <- aux_0;
      i <- i + 1;
    }
    return (d);
  }
  
  proc rol_sum (d:W64.t Array5.t, a:W64.t Array25.t, offset:int) : W64.t Array5.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var c:W64.t Array5.t;
    var j:int;
    var j1:int;
    var k:int;
    var t:W64.t;
    c <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 5) {
      aux <- ((j + offset) %% 5);
      j1 <- aux;
      aux <@ rhotates (j, j1);
      k <- aux;
      leakages <- LeakAddr([((5 * (j %% 5)) + (j1 %% 5))]) :: leakages;
      aux_0 <- a.[((5 * (j %% 5)) + (j1 %% 5))];
      t <- aux_0;
      leakages <- LeakAddr([j1]) :: leakages;
      aux_0 <- (t `^` d.[j1]);
      t <- aux_0;
      aux_0 <@ rOL64 (t, k);
      t <- aux_0;
      aux_0 <- t;
      leakages <- LeakAddr([j]) :: leakages;
      c.[j] <- aux_0;
      j <- j + 1;
    }
    return (c);
  }
  
  proc set_row (r:W64.t Array25.t, row:int, c:W64.t Array5.t, iota_0:W64.t) : 
  W64.t Array25.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var j:int;
    var j1:int;
    var j2:int;
    var t:W64.t;
    
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    j <- 0;
    while (j < 5) {
      aux <- ((j + 1) %% 5);
      j1 <- aux;
      aux <- ((j + 2) %% 5);
      j2 <- aux;
      leakages <- LeakAddr([j2] ++ [j1]) :: leakages;
      aux_0 <- ((invw c.[j1]) `&` c.[j2]);
      t <- aux_0;
      leakages <- LeakCond(((row = 0) /\ (j = 0))) :: LeakAddr([]) :: leakages;
      if (((row = 0) /\ (j = 0))) {
        aux_0 <- (t `^` iota_0);
        t <- aux_0;
      } else {
        
      }
      leakages <- LeakAddr([j]) :: leakages;
      aux_0 <- (t `^` c.[j]);
      t <- aux_0;
      aux_0 <- t;
      leakages <- LeakAddr([((5 * (row %% 5)) + (j %% 5))]) :: leakages;
      r.[((5 * (row %% 5)) + (j %% 5))] <- aux_0;
      j <- j + 1;
    }
    return (r);
  }
  
  proc round2x (a:W64.t Array25.t, r:W64.t Array25.t, iotas:W64.t, o:int) : 
  W64.t Array25.t * W64.t Array25.t = {
    var aux: W64.t;
    var aux_0: W64.t Array5.t;
    var aux_1: W64.t Array25.t;
    
    var iota_0:W64.t;
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;
    c <- witness;
    d <- witness;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (iotas + (W64.of_int o))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (iotas + (W64.of_int o))));
    iota_0 <- aux;
    aux_0 <@ theta_sum (a);
    c <- aux_0;
    aux_0 <@ theta_rol (c);
    d <- aux_0;
    aux_0 <@ rol_sum (d, a, 0);
    c <- aux_0;
    aux_1 <@ set_row (r, 0, c, iota_0);
    r <- aux_1;
    aux_0 <@ rol_sum (d, a, 3);
    c <- aux_0;
    aux_1 <@ set_row (r, 1, c, iota_0);
    r <- aux_1;
    aux_0 <@ rol_sum (d, a, 1);
    c <- aux_0;
    aux_1 <@ set_row (r, 2, c, iota_0);
    r <- aux_1;
    aux_0 <@ rol_sum (d, a, 4);
    c <- aux_0;
    aux_1 <@ set_row (r, 3, c, iota_0);
    r <- aux_1;
    aux_0 <@ rol_sum (d, a, 2);
    c <- aux_0;
    aux_1 <@ set_row (r, 4, c, iota_0);
    r <- aux_1;
    return (a, r);
  }
  
  proc __keccakf1600_scalar (a:W64.t Array25.t, iotas:W64.t) : W64.t Array25.t *
                                                               W64.t = {
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: W64.t;
    var aux_0: W64.t Array25.t;
    var aux: W64.t Array25.t;
    
    var zf:bool;
    var r:W64.t Array25.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    r <- witness;
    (aux_0, aux) <@ round2x (a, r, iotas, 0);
    a <- aux_0;
    r <- aux;
    (aux_0, aux) <@ round2x (r, a, iotas, 8);
    r <- aux_0;
    a <- aux;
    aux_1 <- (iotas + (W64.of_int 16));
    iotas <- aux_1;
    (aux_6, aux_5, aux_4, aux_3, aux_2) <- TEST_8 (truncateu8 iotas)
    (W8.of_int 255);
     _0 <- aux_6;
     _1 <- aux_5;
     _2 <- aux_4;
     _3 <- aux_3;
    zf <- aux_2;
    leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
    
    while ((! zf)) {
      (aux_0, aux) <@ round2x (a, r, iotas, 0);
      a <- aux_0;
      r <- aux;
      (aux_0, aux) <@ round2x (r, a, iotas, 8);
      r <- aux_0;
      a <- aux;
      aux_1 <- (iotas + (W64.of_int 16));
      iotas <- aux_1;
      (aux_6, aux_5, aux_4, aux_3, aux_2) <- TEST_8 (truncateu8 iotas)
      (W8.of_int 255);
       _0 <- aux_6;
       _1 <- aux_5;
       _2 <- aux_4;
       _3 <- aux_3;
      zf <- aux_2;
    leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
    
    }
    aux_1 <- (iotas - (W64.of_int 192));
    iotas <- aux_1;
    return (a, iotas);
  }
  
  proc spill_2 (a:W64.t, b:W64.t) : W64.t * W64.t = {
    var aux: W64.t;
    
    var sa:W64.t;
    var sb:W64.t;
    
    aux <- a;
    sa <- aux;
    aux <- b;
    sb <- aux;
    return (sa, sb);
  }
  
  proc spill_3 (a:W64.t, b:W64.t, c:W64.t) : W64.t * W64.t * W64.t = {
    var aux: W64.t;
    
    var sa:W64.t;
    var sb:W64.t;
    var sc:W64.t;
    
    aux <- a;
    sa <- aux;
    aux <- b;
    sb <- aux;
    aux <- c;
    sc <- aux;
    return (sa, sb, sc);
  }
  
  proc load_2 (sa:W64.t, sb:W64.t) : W64.t * W64.t = {
    var aux: W64.t;
    
    var a:W64.t;
    var b:W64.t;
    
    aux <- sa;
    a <- aux;
    aux <- sb;
    b <- aux;
    return (a, b);
  }
  
  proc load_3 (sa:W64.t, sb:W64.t, sc:W64.t) : W64.t * W64.t * W64.t = {
    var aux: W64.t;
    
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    
    aux <- sa;
    a <- aux;
    aux <- sb;
    b <- aux;
    aux <- sc;
    c <- aux;
    return (a, b, c);
  }
  
  proc keccak_init () : W64.t Array25.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var state:W64.t Array25.t;
    var t:W64.t;
    var i:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    state <- witness;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_64 ;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
     _4 <- aux;
    t <- aux_4;
    aux_4 <- (W64.of_int 0);
    i <- aux_4;
    
    leakages <- LeakCond((i \ult (W64.of_int 25))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 25))) {
      aux_4 <- t;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      state.[(W64.to_uint i)] <- aux_4;
      aux_4 <- (i + (W64.of_int 1));
      i <- aux_4;
    leakages <- LeakCond((i \ult (W64.of_int 25))) :: LeakAddr([]) :: leakages;
    
    }
    return (state);
  }
  
  proc add_full_block (state:W64.t Array25.t, in_0:W64.t, inlen:W64.t,
                       rate:W64.t) : W64.t Array25.t * W64.t * W64.t = {
    var aux: W64.t;
    
    var rate64:W64.t;
    var i:W64.t;
    var t:W64.t;
    
    aux <- rate;
    rate64 <- aux;
    aux <- (rate64 `>>` (W8.of_int 3));
    rate64 <- aux;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult rate64)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult rate64)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + ((W64.of_int 8) * i))))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))));
      t <- aux;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- (state.[(W64.to_uint i)] `^` t);
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      state.[(W64.to_uint i)] <- aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult rate64)) :: LeakAddr([]) :: leakages;
    
    }
    aux <- (in_0 + rate);
    in_0 <- aux;
    aux <- (inlen - rate);
    inlen <- aux;
    return (state, in_0, inlen);
  }
  
  proc add_final_block (state:W64.t Array25.t, in_0:W64.t, inlen:W64.t,
                        trail_byte:W8.t, rate:W64.t) : W64.t Array25.t = {
    var aux_0: W8.t;
    var aux: W64.t;
    
    var inlen8:W64.t;
    var i:W64.t;
    var t:W64.t;
    var c:W8.t;
    
    aux <- inlen;
    inlen8 <- aux;
    aux <- (inlen8 `>>` (W8.of_int 3));
    inlen8 <- aux;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult inlen8)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult inlen8)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + ((W64.of_int 8) * i))))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))));
      t <- aux;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- (state.[(W64.to_uint i)] `^` t);
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      state.[(W64.to_uint i)] <- aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult inlen8)) :: LeakAddr([]) :: leakages;
    
    }
    aux <- (i `<<` (W8.of_int 3));
    i <- aux;
    
    leakages <- LeakCond((i \ult inlen)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult inlen)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + i)))]) :: leakages;
      aux_0 <- (loadW8 Glob.mem (W64.to_uint (in_0 + i)));
      c <- aux_0;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_0 <- ((get8 (WArray200.init64 (fun i => state.[i]))
                (W64.to_uint i)) `^` c);
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      state <-
      Array25.init
      (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint i) aux_0));
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult inlen)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
    aux_0 <- ((get8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint i)) `^` trail_byte);
    leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint i) aux_0));
    aux <- rate;
    i <- aux;
    aux <- (i - (W64.of_int 1));
    i <- aux;
    leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
    aux_0 <- ((get8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint i)) `^` (W8.of_int 128));
    leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
    state <-
    Array25.init
    (WArray200.get64 (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint i) aux_0));
    return (state);
  }
  
  proc absorb (state:W64.t Array25.t, iotas:W64.t, in_0:W64.t, inlen:W64.t,
               s_trail_byte:W64.t, rate:W64.t) : W64.t Array25.t * W64.t *
                                                 W64.t = {
    var aux_3: W8.t;
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux: W64.t Array25.t;
    
    var s_in:W64.t;
    var s_inlen:W64.t;
    var s_rate:W64.t;
    var t:W64.t;
    var trail_byte:W8.t;
    
    
    leakages <- LeakCond((rate \ule inlen)) :: LeakAddr([]) :: leakages;
    
    while ((rate \ule inlen)) {
      (aux, aux_2, aux_1) <@ add_full_block (state, in_0, inlen, rate);
      state <- aux;
      in_0 <- aux_2;
      inlen <- aux_1;
      (aux_2, aux_1, aux_0) <@ spill_3 (in_0, inlen, rate);
      s_in <- aux_2;
      s_inlen <- aux_1;
      s_rate <- aux_0;
      (aux, aux_2) <@ __keccakf1600_scalar (state, iotas);
      state <- aux;
      iotas <- aux_2;
      (aux_2, aux_1, aux_0) <@ load_3 (s_in, s_inlen, s_rate);
      in_0 <- aux_2;
      inlen <- aux_1;
      rate <- aux_0;
    leakages <- LeakCond((rate \ule inlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux_2 <- s_trail_byte;
    t <- aux_2;
    aux_2 <- t;
    trail_byte <- (truncateu8 aux_2);
    aux <@ add_final_block (state, in_0, inlen, trail_byte, rate);
    state <- aux;
    return (state, iotas, rate);
  }
  
  proc xtr_full_block (state:W64.t Array25.t, out:W64.t, outlen:W64.t,
                       rate:W64.t) : W64.t * W64.t = {
    var aux: W64.t;
    
    var rate64:W64.t;
    var i:W64.t;
    var t:W64.t;
    
    aux <- rate;
    rate64 <- aux;
    aux <- (rate64 `>>` (W8.of_int 3));
    rate64 <- aux;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult rate64)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult rate64)) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- state.[(W64.to_uint i)];
      t <- aux;
      aux <- t;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + ((W64.of_int 8) * i))))]) :: leakages;
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + ((W64.of_int 8) * i))) aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult rate64)) :: LeakAddr([]) :: leakages;
    
    }
    aux <- (out + rate);
    out <- aux;
    aux <- (outlen - rate);
    outlen <- aux;
    return (out, outlen);
  }
  
  proc xtr_bytes (state:W64.t Array25.t, out:W64.t, outlen:W64.t) : W64.t = {
    var aux_0: W8.t;
    var aux: W64.t;
    
    var outlen8:W64.t;
    var i:W64.t;
    var t:W64.t;
    var c:W8.t;
    
    aux <- outlen;
    outlen8 <- aux;
    aux <- (outlen8 `>>` (W8.of_int 3));
    outlen8 <- aux;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult outlen8)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult outlen8)) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- state.[(W64.to_uint i)];
      t <- aux;
      aux <- t;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + ((W64.of_int 8) * i))))]) :: leakages;
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + ((W64.of_int 8) * i))) aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult outlen8)) :: LeakAddr([]) :: leakages;
    
    }
    aux <- (i `<<` (W8.of_int 3));
    i <- aux;
    
    leakages <- LeakCond((i \ult outlen)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult outlen)) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_0 <- (get8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint i));
      c <- aux_0;
      aux_0 <- c;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + i)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + i)) aux_0;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult outlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux <- (out + outlen);
    out <- aux;
    return (out);
  }
  
  proc squeeze (state:W64.t Array25.t, iotas:W64.t, s_out:W64.t,
                outlen:W64.t, rate:W64.t) : unit = {
    var aux_2: W64.t;
    var aux_0: W64.t;
    var aux: W64.t;
    var aux_1: W64.t Array25.t;
    
    var s_outlen:W64.t;
    var s_rate:W64.t;
    var out:W64.t;
    
    
    leakages <- LeakCond((rate \ult outlen)) :: LeakAddr([]) :: leakages;
    
    while ((rate \ult outlen)) {
      (aux_2, aux_0) <@ spill_2 (outlen, rate);
      s_outlen <- aux_2;
      s_rate <- aux_0;
      (aux_1, aux_2) <@ __keccakf1600_scalar (state, iotas);
      state <- aux_1;
      iotas <- aux_2;
      (aux_2, aux_0, aux) <@ load_3 (s_out, s_outlen, s_rate);
      out <- aux_2;
      outlen <- aux_0;
      rate <- aux;
      (aux_2, aux_0) <@ xtr_full_block (state, out, outlen, rate);
      out <- aux_2;
      outlen <- aux_0;
      aux_2 <- out;
      s_out <- aux_2;
    leakages <- LeakCond((rate \ult outlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux_2 <- outlen;
    s_outlen <- aux_2;
    (aux_1, aux_2) <@ __keccakf1600_scalar (state, iotas);
    state <- aux_1;
    iotas <- aux_2;
    (aux_2, aux_0) <@ load_2 (s_out, s_outlen);
    out <- aux_2;
    outlen <- aux_0;
    aux_2 <@ xtr_bytes (state, out, outlen);
    out <- aux_2;
    return ();
  }
  
  proc __keccak1600_scalar (s_out:W64.t, s_outlen:W64.t, iotas:W64.t,
                            in_0:W64.t, inlen:W64.t, s_trail_byte:W64.t,
                            rate:W64.t) : unit = {
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux: W64.t Array25.t;
    
    var state:W64.t Array25.t;
    var outlen:W64.t;
    state <- witness;
    aux <@ keccak_init ();
    state <- aux;
    (aux, aux_1, aux_0) <@ absorb (state, iotas, in_0, inlen, s_trail_byte,
    rate);
    state <- aux;
    iotas <- aux_1;
    rate <- aux_0;
    aux_1 <- s_outlen;
    outlen <- aux_1;
    squeeze (state, iotas, s_out, outlen, rate);
    return ();
  }
  
  proc keccak1600_scalar (out:W64.t, outlen:W64.t, in_0:W64.t, inlen_:W64.t,
                          config:W64.t, iotas:W64.t) : unit = {
    var aux: W64.t;
    
    var s_out:W64.t;
    var s_outlen:W64.t;
    var inlen:W64.t;
    var trail_byte:W64.t;
    var s_trail_byte:W64.t;
    var rate:W64.t;
    
    aux <- out;
    s_out <- aux;
    aux <- outlen;
    s_outlen <- aux;
    aux <- inlen_;
    inlen <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (config + (W64.of_int (8 * 0)))))]) :: leakages;
    aux <- (zeroextu64 (loadW8 Glob.mem (W64.to_uint (config + (W64.of_int (8 * 0))))));
    trail_byte <- aux;
    aux <- trail_byte;
    s_trail_byte <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (config + (W64.of_int (8 * 1)))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (config + (W64.of_int (8 * 1)))));
    rate <- aux;
    __keccak1600_scalar (s_out, s_outlen, iotas, in_0, inlen, s_trail_byte,
    rate);
    return ();
  }
}.
end T.

