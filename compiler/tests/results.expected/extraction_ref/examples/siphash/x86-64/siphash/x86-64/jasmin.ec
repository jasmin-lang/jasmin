require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array4.
require import WArray16 WArray32.



module M = {
  proc sipround (v:W64.t Array4.t) : W64.t Array4.t = {
    
    
    
    v.[0] <- (v.[0] + v.[1]);
    v.[1] <- (v.[1] `|<<|` (W8.of_int 13));
    v.[1] <- (v.[1] `^` v.[0]);
    v.[0] <- (v.[0] `|<<|` (W8.of_int 32));
    v.[2] <- (v.[2] + v.[3]);
    v.[3] <- (v.[3] `|<<|` (W8.of_int 16));
    v.[3] <- (v.[3] `^` v.[2]);
    v.[0] <- (v.[0] + v.[3]);
    v.[3] <- (v.[3] `|<<|` (W8.of_int 21));
    v.[3] <- (v.[3] `^` v.[0]);
    v.[2] <- (v.[2] + v.[1]);
    v.[1] <- (v.[1] `|<<|` (W8.of_int 17));
    v.[1] <- (v.[1] `^` v.[2]);
    v.[2] <- (v.[2] `|<<|` (W8.of_int 32));
    return (v);
  }
  
  proc siphash_jazz (in_0:W64.t, inlen:W64.t, kptr:W64.t, out:W64.t, outlen:W64.t) : unit = {
    var aux: int;
    
    var v:W64.t Array4.t;
    var k:W64.t Array2.t;
    var left_0:W64.t;
    var b:W64.t;
    var end_0:W64.t;
    var m:W64.t;
    var i:int;
    var x:W64.t;
    k <- witness;
    v <- witness;
    v.[0] <- (W64.of_int 8317987319222330741);
    v.[1] <- (W64.of_int 7237128888997146477);
    v.[2] <- (W64.of_int 7816392313619706465);
    v.[3] <- (W64.of_int 8387220255154660723);
    k.[0] <- (loadW64 Glob.mem (W64.to_uint (kptr + (W64.of_int (0 * 8)))));
    k.[1] <- (loadW64 Glob.mem (W64.to_uint (kptr + (W64.of_int (1 * 8)))));
    v.[3] <- (v.[3] `^` k.[1]);
    v.[2] <- (v.[2] `^` k.[0]);
    v.[1] <- (v.[1] `^` k.[1]);
    v.[0] <- (v.[0] `^` k.[0]);
    if ((outlen = (W64.of_int 16))) {
      v.[1] <- (v.[1] `^` (W64.of_int 238));
    } else {
      
    }
    left_0 <- inlen;
    left_0 <- (left_0 `&` (W64.of_int 7));
    b <- inlen;
    b <- (b `<<` (W8.of_int 56));
    inlen <- (inlen `&` (W64.of_int 18446744073709551608));
    end_0 <- LEA_64 (in_0 + inlen);
    
    while ((in_0 <> end_0)) {
      m <- (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (0 * 8)))));
      v.[3] <- (v.[3] `^` m);
      i <- 0;
      while (i < 2) {
        v <@ sipround (v);
        i <- i + 1;
      }
      v.[0] <- (v.[0] `^` m);
      in_0 <- (in_0 + (W64.of_int 8));
    }
    if (((W64.of_int 1) \ule left_0)) {
      x <- (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (0 * 8)))));
      if ((left_0 \ult (W64.of_int 4))) {
        if ((left_0 \ult (W64.of_int 2))) {
          x <- (x `&` (W64.of_int 255));
        } else {
          if ((left_0 = (W64.of_int 2))) {
            x <- (x `&` (W64.of_int 65535));
          } else {
            x <- (x `&` (W64.of_int 16777215));
          }
        }
      } else {
        if ((left_0 \ult (W64.of_int 6))) {
          if ((left_0 = (W64.of_int 4))) {
            x <- (x `&` (W64.of_int 4294967295));
          } else {
            x <- (x `&` (W64.of_int 1099511627775));
          }
        } else {
          if ((left_0 = (W64.of_int 6))) {
            x <- (x `&` (W64.of_int 281474976710655));
          } else {
            x <- (x `&` (W64.of_int 72057594037927935));
          }
        }
      }
      b <- (b `|` x);
    } else {
      
    }
    v.[3] <- (v.[3] `^` b);
    i <- 0;
    while (i < 2) {
      v <@ sipround (v);
      i <- i + 1;
    }
    v.[0] <- (v.[0] `^` b);
    if ((outlen = (W64.of_int 16))) {
      v.[2] <- (v.[2] `^` (W64.of_int 238));
    } else {
      v.[2] <- (v.[2] `^` (W64.of_int 255));
    }
    i <- 0;
    while (i < 4) {
      v <@ sipround (v);
      i <- i + 1;
    }
    b <- v.[0];
    b <- (b `^` v.[1]);
    b <- (b `^` v.[2]);
    b <- (b `^` v.[3]);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (0 * 8)))) (b);
    if ((outlen = (W64.of_int 16))) {
      v.[1] <- (v.[1] `^` (W64.of_int 221));
      i <- 0;
      while (i < 4) {
        v <@ sipround (v);
        i <- i + 1;
      }
      b <- v.[0];
      b <- (b `^` v.[1]);
      b <- (b `^` v.[2]);
      b <- (b `^` v.[3]);
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (1 * 8)))) (b);
    } else {
      
    }
    return ();
  }
}.

