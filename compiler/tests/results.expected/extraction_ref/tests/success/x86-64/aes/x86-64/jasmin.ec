require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array11.
require import WArray176.



module M = {
  proc rCON (i:int) : int = {
    
    var c:int;
    
    c <- ((i = 1) ? 1 : ((i = 2) ? 2 : ((i = 3) ? 4 : ((i = 4) ? 8 : ((i = 5) ? 16 : ((i = 6) ? 32 : ((i = 7) ? 64 : ((i = 8) ? 128 : ((i = 9) ? 27 : 54)))))))));
    return (c);
  }
  
  proc addRoundKey (state:W128.t, rk:W128.t) : W128.t = {
    
    
    
    state <- (state `^` rk);
    return (state);
  }
  
  proc cipher (in_0:W128.t, rks:W128.t Array11.t) : W128.t = {
    var aux: int;
    
    var state:W128.t;
    var round:int;
    
    state <- in_0;
    state <- (state `^` rks.[0]);
    round <- 1;
    while (round < 10) {
      state <- AESENC state rks.[round];
      round <- round + 1;
    }
    state <- AESENCLAST state rks.[10];
    return (state);
  }
  
  proc key_combine (rkey:W128.t, temp1:W128.t, temp2:W128.t) : W128.t * W128.t = {
    
    
    
    temp1 <- VPSHUFD_128 temp1 (W8.of_int (3 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 3))));
    temp2 <- VSHUFPS_128 temp2 rkey (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    rkey <- (rkey `^` temp2);
    temp2 <- VSHUFPS_128 temp2 rkey (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    rkey <- (rkey `^` temp2);
    rkey <- (rkey `^` temp1);
    return (rkey, temp2);
  }
  
  proc key_expand (rcon:int, rkey:W128.t, temp2:W128.t) : W128.t * W128.t = {
    
    var temp1:W128.t;
    
    temp1 <- VAESKEYGENASSIST rkey (W8.of_int rcon);
    (rkey, temp2) <@ key_combine (rkey, temp1, temp2);
    return (rkey, temp2);
  }
  
  proc keys_expand (key:W128.t) : W128.t Array11.t = {
    var aux: int;
    
    var rkeys:W128.t Array11.t;
    var temp2:W128.t;
    var i:int;
    var rcon:int;
    rkeys <- witness;
    rkeys.[0] <- key;
    temp2 <- set0_128 ;
    i <- 1;
    while (i < 11) {
      rcon <@ rCON (i);
      (key, temp2) <@ key_expand (rcon, key, temp2);
      rkeys.[i] <- key;
      i <- i + 1;
    }
    return (rkeys);
  }
  
  proc _aes_enc (key:W128.t, in_0:W128.t) : W128.t = {
    
    var out:W128.t;
    var rkeys:W128.t Array11.t;
    rkeys <- witness;
    rkeys <@ keys_expand (key);
    out <@ cipher (in_0, rkeys);
    return (out);
  }
  
  proc aes_enc (pkey:W64.t, pin:W64.t, pout:W64.t) : unit = {
    
    var in_0:W128.t;
    var key:W128.t;
    var out:W128.t;
    
    in_0 <- (loadW128 Glob.mem (W64.to_uint (pin + (W64.of_int 0))));
    key <- (loadW128 Glob.mem (W64.to_uint (pkey + (W64.of_int 0))));
    out <@ _aes_enc (key, in_0);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (pout + (W64.of_int 0))) (out);
    return ();
  }
}.

