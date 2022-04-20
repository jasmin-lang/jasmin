require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.

require import Array5 Array24 Array25.
require import WArray40 WArray192 WArray200.


theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t
  
  proc index (x:int, y:int) : int = {
    var aux: int;
    
    var r:int;
    
    aux <- ((x %% 5) + (5 * (y %% 5)));
    r <- aux;
    return (r);
  }
  
  proc theta (a:W64.t Array25.t) : W64.t Array25.t = {
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var x:int;
    var c:W64.t Array5.t;
    var y:int;
    var d:W64.t Array5.t;
    var  _0:bool;
    var  _1:bool;
    c <- witness;
    d <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    x <- 0;
    while (x < 5) {
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([x]) :: leakages;
      c.[x] <- aux_0;
      leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
      y <- 0;
      while (y < 5) {
        leakages <- LeakAddr([(x + (5 * y))] ++ [x]) :: leakages;
        aux_0 <- (c.[x] `^` a.[(x + (5 * y))]);
        leakages <- LeakAddr([x]) :: leakages;
        c.[x] <- aux_0;
        y <- y + 1;
      }
      x <- x + 1;
    }
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    x <- 0;
    while (x < 5) {
      leakages <- LeakAddr([((x + 1) %% 5)]) :: leakages;
      aux_0 <- c.[((x + 1) %% 5)];
      leakages <- LeakAddr([x]) :: leakages;
      d.[x] <- aux_0;
      leakages <- LeakAddr([x]) :: leakages;
      (aux_2, aux_1, aux_0) <- ROL_64 d.[x] (W8.of_int 1);
       _0 <- aux_2;
       _1 <- aux_1;
      leakages <- LeakAddr([x]) :: leakages;
      d.[x] <- aux_0;
      leakages <- LeakAddr([((x + 4) %% 5)] ++ [x]) :: leakages;
      aux_0 <- (d.[x] `^` c.[((x + 4) %% 5)]);
      leakages <- LeakAddr([x]) :: leakages;
      d.[x] <- aux_0;
      x <- x + 1;
    }
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    x <- 0;
    while (x < 5) {
      leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
      y <- 0;
      while (y < 5) {
        leakages <- LeakAddr([x] ++ [(x + (5 * y))]) :: leakages;
        aux_0 <- (a.[(x + (5 * y))] `^` d.[x]);
        leakages <- LeakAddr([(x + (5 * y))]) :: leakages;
        a.[(x + (5 * y))] <- aux_0;
        y <- y + 1;
      }
      x <- x + 1;
    }
    return (a);
  }
  
  proc keccakRhoOffsets (i:int) : int = {
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
  
  proc rho (a:W64.t Array25.t) : W64.t Array25.t = {
    var aux_1: bool;
    var aux_0: bool;
    var aux: int;
    var aux_2: W64.t;
    
    var x:int;
    var y:int;
    var i:int;
    var z:int;
    var  _0:bool;
    var  _1:bool;
    
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    x <- 0;
    while (x < 5) {
      leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
      y <- 0;
      while (y < 5) {
        aux <@ index (x, y);
        i <- aux;
        aux <@ keccakRhoOffsets (i);
        z <- aux;
        leakages <- LeakAddr([i]) :: leakages;
        (aux_1, aux_0, aux_2) <- ROL_64 a.[i] (W8.of_int z);
         _0 <- aux_1;
         _1 <- aux_0;
        leakages <- LeakAddr([i]) :: leakages;
        a.[i] <- aux_2;
        y <- y + 1;
      }
      x <- x + 1;
    }
    return (a);
  }
  
  proc pi (a:W64.t Array25.t) : W64.t Array25.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var t:W64.t;
    var b:W64.t Array25.t;
    var y:int;
    var x:int;
    b <- witness;
    leakages <- LeakFor(0,25) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 25) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      b.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    x <- 0;
    while (x < 5) {
      leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
      y <- 0;
      while (y < 5) {
        leakages <- LeakAddr([(x + (5 * y))]) :: leakages;
        aux_0 <- b.[(x + (5 * y))];
        t <- aux_0;
        aux <@ index (y, ((2 * x) + (3 * y)));
        i <- aux;
        aux_0 <- t;
        leakages <- LeakAddr([i]) :: leakages;
        a.[i] <- aux_0;
        y <- y + 1;
      }
      x <- x + 1;
    }
    return (a);
  }
  
  proc chi (a:W64.t Array25.t) : W64.t Array25.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var x:int;
    var y:int;
    var i:int;
    var c:W64.t Array5.t;
    c <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    y <- 0;
    while (y < 5) {
      leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
      x <- 0;
      while (x < 5) {
        aux <@ index ((x + 1), y);
        i <- aux;
        leakages <- LeakAddr([i]) :: leakages;
        aux_0 <- a.[i];
        leakages <- LeakAddr([x]) :: leakages;
        c.[x] <- aux_0;
        leakages <- LeakAddr([x]) :: leakages;
        aux_0 <- (invw c.[x]);
        leakages <- LeakAddr([x]) :: leakages;
        c.[x] <- aux_0;
        aux <@ index ((x + 2), y);
        i <- aux;
        leakages <- LeakAddr([i] ++ [x]) :: leakages;
        aux_0 <- (c.[x] `&` a.[i]);
        leakages <- LeakAddr([x]) :: leakages;
        c.[x] <- aux_0;
        aux <@ index (x, y);
        i <- aux;
        leakages <- LeakAddr([i] ++ [x]) :: leakages;
        aux_0 <- (c.[x] `^` a.[i]);
        leakages <- LeakAddr([x]) :: leakages;
        c.[x] <- aux_0;
        x <- x + 1;
      }
      leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
      x <- 0;
      while (x < 5) {
        leakages <- LeakAddr([x]) :: leakages;
        aux_0 <- c.[x];
        leakages <- LeakAddr([(x + (5 * y))]) :: leakages;
        a.[(x + (5 * y))] <- aux_0;
        x <- x + 1;
      }
      y <- y + 1;
    }
    return (a);
  }
  
  proc iota_0 (a:W64.t Array25.t, c:W64.t) : W64.t Array25.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (a.[0] `^` c);
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    return (a);
  }
  
  proc keccakP1600_round (state:W64.t Array25.t, c:W64.t) : W64.t Array25.t = {
    var aux: W64.t Array25.t;
    
    
    
    aux <@ theta (state);
    state <- aux;
    aux <@ rho (state);
    state <- aux;
    aux <@ pi (state);
    state <- aux;
    aux <@ chi (state);
    state <- aux;
    aux <@ iota_0 (state, c);
    state <- aux;
    return (state);
  }
  
  proc keccakRoundConstants () : W64.t Array24.t = {
    var aux: W64.t;
    
    var constants:W64.t Array24.t;
    var t:W64.t;
    constants <- witness;
    aux <- (W64.of_int 1);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([0]) :: leakages;
    constants.[0] <- aux;
    aux <- (W64.of_int 32898);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([1]) :: leakages;
    constants.[1] <- aux;
    aux <- (W64.of_int 9223372036854808714);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([2]) :: leakages;
    constants.[2] <- aux;
    aux <- (W64.of_int 9223372039002292224);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([3]) :: leakages;
    constants.[3] <- aux;
    aux <- (W64.of_int 32907);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([4]) :: leakages;
    constants.[4] <- aux;
    aux <- (W64.of_int 2147483649);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([5]) :: leakages;
    constants.[5] <- aux;
    aux <- (W64.of_int 9223372039002292353);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([6]) :: leakages;
    constants.[6] <- aux;
    aux <- (W64.of_int 9223372036854808585);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([7]) :: leakages;
    constants.[7] <- aux;
    aux <- (W64.of_int 138);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([8]) :: leakages;
    constants.[8] <- aux;
    aux <- (W64.of_int 136);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([9]) :: leakages;
    constants.[9] <- aux;
    aux <- (W64.of_int 2147516425);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([10]) :: leakages;
    constants.[10] <- aux;
    aux <- (W64.of_int 2147483658);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([11]) :: leakages;
    constants.[11] <- aux;
    aux <- (W64.of_int 2147516555);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([12]) :: leakages;
    constants.[12] <- aux;
    aux <- (W64.of_int 9223372036854775947);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([13]) :: leakages;
    constants.[13] <- aux;
    aux <- (W64.of_int 9223372036854808713);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([14]) :: leakages;
    constants.[14] <- aux;
    aux <- (W64.of_int 9223372036854808579);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([15]) :: leakages;
    constants.[15] <- aux;
    aux <- (W64.of_int 9223372036854808578);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([16]) :: leakages;
    constants.[16] <- aux;
    aux <- (W64.of_int 9223372036854775936);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([17]) :: leakages;
    constants.[17] <- aux;
    aux <- (W64.of_int 32778);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([18]) :: leakages;
    constants.[18] <- aux;
    aux <- (W64.of_int 9223372039002259466);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([19]) :: leakages;
    constants.[19] <- aux;
    aux <- (W64.of_int 9223372039002292353);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([20]) :: leakages;
    constants.[20] <- aux;
    aux <- (W64.of_int 9223372036854808704);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([21]) :: leakages;
    constants.[21] <- aux;
    aux <- (W64.of_int 2147483649);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([22]) :: leakages;
    constants.[22] <- aux;
    aux <- (W64.of_int 9223372039002292232);
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([23]) :: leakages;
    constants.[23] <- aux;
    return (constants);
  }
  
  proc __keccakf1600_ref (state:W64.t Array25.t) : W64.t Array25.t = {
    var aux_0: int;
    var aux: W64.t Array24.t;
    var aux_1: W64.t Array25.t;
    
    var constants:W64.t Array24.t;
    var round:int;
    constants <- witness;
    aux <@ keccakRoundConstants ();
    constants <- aux;
    leakages <- LeakFor(0,24) :: LeakAddr([]) :: leakages;
    round <- 0;
    while (round < 24) {
      leakages <- LeakAddr([round]) :: leakages;
      aux_1 <@ keccakP1600_round (state, constants.[round]);
      state <- aux_1;
      round <- round + 1;
    }
    return (state);
  }
  
  proc st0 () : W64.t Array25.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var state:W64.t Array25.t;
    var i:int;
    state <- witness;
    leakages <- LeakFor(0,25) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 25) {
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      state.[i] <- aux_0;
      i <- i + 1;
    }
    return (state);
  }
  
  proc add_full_block (state:W64.t Array25.t, in_0:W64.t, inlen:W64.t,
                       r8:W64.t) : W64.t Array25.t * W64.t * W64.t = {
    var aux: W64.t;
    
    var r64:W64.t;
    var i:W64.t;
    var t:W64.t;
    
    aux <- r8;
    r64 <- aux;
    aux <- (r64 `>>` (W8.of_int 3));
    r64 <- aux;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult r64)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult r64)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + ((W64.of_int 8) * i))))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))));
      t <- aux;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- (state.[(W64.to_uint i)] `^` t);
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      state.[(W64.to_uint i)] <- aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult r64)) :: LeakAddr([]) :: leakages;
    
    }
    aux <- (in_0 + r8);
    in_0 <- aux;
    aux <- (inlen - r8);
    inlen <- aux;
    return (state, in_0, inlen);
  }
  
  proc add_final_block (state:W64.t Array25.t, in_0:W64.t, inlen:W64.t,
                        trail_byte:W8.t, r8:W64.t) : W64.t Array25.t = {
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
    aux <- r8;
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
  
  proc xtr_bytes (state:W64.t Array25.t, out:W64.t, outlen:W64.t) : unit = {
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
    return ();
  }
  
  proc __keccak1600_ref (s_out:W64.t, s_outlen:W64.t, in_0:W64.t,
                         inlen:W64.t, s_trail_byte:W64.t, rate:W64.t) : unit = {
    var aux_2: W8.t;
    var aux_1: W64.t;
    var aux_0: W64.t;
    var aux: W64.t Array25.t;
    
    var state:W64.t Array25.t;
    var s_in:W64.t;
    var s_inlen:W64.t;
    var s_rate:W64.t;
    var t:W64.t;
    var trail_byte:W8.t;
    var outlen:W64.t;
    var out:W64.t;
    state <- witness;
    aux <@ st0 ();
    state <- aux;
    
    leakages <- LeakCond((rate \ule inlen)) :: LeakAddr([]) :: leakages;
    
    while ((rate \ule inlen)) {
      (aux, aux_1, aux_0) <@ add_full_block (state, in_0, inlen, rate);
      state <- aux;
      in_0 <- aux_1;
      inlen <- aux_0;
      aux_1 <- in_0;
      s_in <- aux_1;
      aux_1 <- inlen;
      s_inlen <- aux_1;
      aux_1 <- rate;
      s_rate <- aux_1;
      aux <@ __keccakf1600_ref (state);
      state <- aux;
      aux_1 <- s_inlen;
      inlen <- aux_1;
      aux_1 <- s_in;
      in_0 <- aux_1;
      aux_1 <- s_rate;
      rate <- aux_1;
    leakages <- LeakCond((rate \ule inlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux_1 <- s_trail_byte;
    t <- aux_1;
    aux_1 <- t;
    trail_byte <- (truncateu8 aux_1);
    aux <@ add_final_block (state, in_0, inlen, trail_byte, rate);
    state <- aux;
    aux_1 <- s_outlen;
    outlen <- aux_1;
    
    leakages <- LeakCond((rate \ult outlen)) :: LeakAddr([]) :: leakages;
    
    while ((rate \ult outlen)) {
      aux_1 <- outlen;
      s_outlen <- aux_1;
      aux_1 <- rate;
      s_rate <- aux_1;
      aux <@ __keccakf1600_ref (state);
      state <- aux;
      aux_1 <- s_out;
      out <- aux_1;
      aux_1 <- s_outlen;
      outlen <- aux_1;
      aux_1 <- s_rate;
      rate <- aux_1;
      (aux_1, aux_0) <@ xtr_full_block (state, out, outlen, rate);
      out <- aux_1;
      outlen <- aux_0;
      aux_1 <- outlen;
      s_outlen <- aux_1;
      aux_1 <- out;
      s_out <- aux_1;
    leakages <- LeakCond((rate \ult outlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux <@ __keccakf1600_ref (state);
    state <- aux;
    aux_1 <- s_out;
    out <- aux_1;
    aux_1 <- s_outlen;
    outlen <- aux_1;
    xtr_bytes (state, out, outlen);
    return ();
  }
  
  proc keccak1600_ref (out:W64.t, outlen:W64.t, in_0:W64.t, inlen:W64.t,
                       config:W64.t) : unit = {
    var aux: W64.t;
    
    var s_out:W64.t;
    var s_outlen:W64.t;
    var trail_byte:W64.t;
    var s_trail_byte:W64.t;
    var rate:W64.t;
    
    aux <- out;
    s_out <- aux;
    aux <- outlen;
    s_outlen <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (config + (W64.of_int (8 * 0)))))]) :: leakages;
    aux <- (zeroextu64 (loadW8 Glob.mem (W64.to_uint (config + (W64.of_int (8 * 0))))));
    trail_byte <- aux;
    aux <- trail_byte;
    s_trail_byte <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (config + (W64.of_int (8 * 1)))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (config + (W64.of_int (8 * 1)))));
    rate <- aux;
    __keccak1600_ref (s_out, s_outlen, in_0, inlen, s_trail_byte, rate);
    return ();
  }
}.
end T.

