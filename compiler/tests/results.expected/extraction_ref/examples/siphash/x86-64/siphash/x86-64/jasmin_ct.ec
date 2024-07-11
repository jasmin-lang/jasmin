require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array4.
require import WArray16 WArray32.



module M = {
  var leakages : leakages_t
  
  proc sipround (v:W64.t Array4.t) : W64.t Array4.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux <- (v.[0] + v.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    v.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (v.[1] `|<<|` (W8.of_int 13));
    leakages <- LeakAddr([1]) :: leakages;
    v.[1] <- aux;
    leakages <- LeakAddr([0; 1]) :: leakages;
    aux <- (v.[1] `^` v.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    v.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (v.[0] `|<<|` (W8.of_int 32));
    leakages <- LeakAddr([0]) :: leakages;
    v.[0] <- aux;
    leakages <- LeakAddr([3; 2]) :: leakages;
    aux <- (v.[2] + v.[3]);
    leakages <- LeakAddr([2]) :: leakages;
    v.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (v.[3] `|<<|` (W8.of_int 16));
    leakages <- LeakAddr([3]) :: leakages;
    v.[3] <- aux;
    leakages <- LeakAddr([2; 3]) :: leakages;
    aux <- (v.[3] `^` v.[2]);
    leakages <- LeakAddr([3]) :: leakages;
    v.[3] <- aux;
    leakages <- LeakAddr([3; 0]) :: leakages;
    aux <- (v.[0] + v.[3]);
    leakages <- LeakAddr([0]) :: leakages;
    v.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (v.[3] `|<<|` (W8.of_int 21));
    leakages <- LeakAddr([3]) :: leakages;
    v.[3] <- aux;
    leakages <- LeakAddr([0; 3]) :: leakages;
    aux <- (v.[3] `^` v.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    v.[3] <- aux;
    leakages <- LeakAddr([1; 2]) :: leakages;
    aux <- (v.[2] + v.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    v.[2] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (v.[1] `|<<|` (W8.of_int 17));
    leakages <- LeakAddr([1]) :: leakages;
    v.[1] <- aux;
    leakages <- LeakAddr([2; 1]) :: leakages;
    aux <- (v.[1] `^` v.[2]);
    leakages <- LeakAddr([1]) :: leakages;
    v.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (v.[2] `|<<|` (W8.of_int 32));
    leakages <- LeakAddr([2]) :: leakages;
    v.[2] <- aux;
    return (v);
  }
  
  proc siphash_jazz (in_0:W64.t, inlen:W64.t, kptr:W64.t, out:W64.t, outlen:W64.t) : unit = {
    var aux_0: int;
    var aux: W64.t;
    var aux_1: W64.t Array4.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 8317987319222330741);
    leakages <- LeakAddr([0]) :: leakages;
    v.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 7237128888997146477);
    leakages <- LeakAddr([1]) :: leakages;
    v.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 7816392313619706465);
    leakages <- LeakAddr([2]) :: leakages;
    v.[2] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 8387220255154660723);
    leakages <- LeakAddr([3]) :: leakages;
    v.[3] <- aux;
    leakages <- LeakAddr([(W64.to_uint (kptr + (W64.of_int (0 * 8))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (kptr + (W64.of_int (0 * 8)))));
    leakages <- LeakAddr([0]) :: leakages;
    k.[0] <- aux;
    leakages <- LeakAddr([(W64.to_uint (kptr + (W64.of_int (1 * 8))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (kptr + (W64.of_int (1 * 8)))));
    leakages <- LeakAddr([1]) :: leakages;
    k.[1] <- aux;
    leakages <- LeakAddr([1; 3]) :: leakages;
    aux <- (v.[3] `^` k.[1]);
    leakages <- LeakAddr([3]) :: leakages;
    v.[3] <- aux;
    leakages <- LeakAddr([0; 2]) :: leakages;
    aux <- (v.[2] `^` k.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    v.[2] <- aux;
    leakages <- LeakAddr([1; 1]) :: leakages;
    aux <- (v.[1] `^` k.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    v.[1] <- aux;
    leakages <- LeakAddr([0; 0]) :: leakages;
    aux <- (v.[0] `^` k.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    v.[0] <- aux;
    leakages <- LeakCond((outlen = (W64.of_int 16))) :: LeakAddr([]) :: leakages;
    if ((outlen = (W64.of_int 16))) {
      leakages <- LeakAddr([1]) :: leakages;
      aux <- (v.[1] `^` (W64.of_int 238));
      leakages <- LeakAddr([1]) :: leakages;
      v.[1] <- aux;
    } else {
      
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- inlen;
    left_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (left_0 `&` (W64.of_int 7));
    left_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- inlen;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (b `<<` (W8.of_int 56));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (inlen `&` (W64.of_int 18446744073709551608));
    inlen <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- LEA_64 (in_0 + inlen);
    end_0 <- aux;
    
    leakages <- LeakCond((in_0 <> end_0)) :: LeakAddr([]) :: leakages;
    
    while ((in_0 <> end_0)) {
      leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int (0 * 8))))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (0 * 8)))));
      m <- aux;
      leakages <- LeakAddr([3]) :: leakages;
      aux <- (v.[3] `^` m);
      leakages <- LeakAddr([3]) :: leakages;
      v.[3] <- aux;
      leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
      i <- 0;
      while (i < 2) {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ sipround (v);
        v <- aux_1;
        i <- i + 1;
      }
      leakages <- LeakAddr([0]) :: leakages;
      aux <- (v.[0] `^` m);
      leakages <- LeakAddr([0]) :: leakages;
      v.[0] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (in_0 + (W64.of_int 8));
      in_0 <- aux;
    leakages <- LeakCond((in_0 <> end_0)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakCond(((W64.of_int 1) \ule left_0)) :: LeakAddr([]) :: leakages;
    if (((W64.of_int 1) \ule left_0)) {
      leakages <- LeakAddr([(W64.to_uint (in_0 + (W64.of_int (0 * 8))))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (0 * 8)))));
      x <- aux;
      leakages <- LeakCond((left_0 \ult (W64.of_int 4))) :: LeakAddr(
      []) :: leakages;
      if ((left_0 \ult (W64.of_int 4))) {
        leakages <- LeakCond((left_0 \ult (W64.of_int 2))) :: LeakAddr(
        []) :: leakages;
        if ((left_0 \ult (W64.of_int 2))) {
          leakages <- LeakAddr([]) :: leakages;
          aux <- (x `&` (W64.of_int 255));
          x <- aux;
        } else {
          leakages <- LeakCond((left_0 = (W64.of_int 2))) :: LeakAddr(
          []) :: leakages;
          if ((left_0 = (W64.of_int 2))) {
            leakages <- LeakAddr([]) :: leakages;
            aux <- (x `&` (W64.of_int 65535));
            x <- aux;
          } else {
            leakages <- LeakAddr([]) :: leakages;
            aux <- (x `&` (W64.of_int 16777215));
            x <- aux;
          }
        }
      } else {
        leakages <- LeakCond((left_0 \ult (W64.of_int 6))) :: LeakAddr(
        []) :: leakages;
        if ((left_0 \ult (W64.of_int 6))) {
          leakages <- LeakCond((left_0 = (W64.of_int 4))) :: LeakAddr(
          []) :: leakages;
          if ((left_0 = (W64.of_int 4))) {
            leakages <- LeakAddr([]) :: leakages;
            aux <- (x `&` (W64.of_int 4294967295));
            x <- aux;
          } else {
            leakages <- LeakAddr([]) :: leakages;
            aux <- (x `&` (W64.of_int 1099511627775));
            x <- aux;
          }
        } else {
          leakages <- LeakCond((left_0 = (W64.of_int 6))) :: LeakAddr(
          []) :: leakages;
          if ((left_0 = (W64.of_int 6))) {
            leakages <- LeakAddr([]) :: leakages;
            aux <- (x `&` (W64.of_int 281474976710655));
            x <- aux;
          } else {
            leakages <- LeakAddr([]) :: leakages;
            aux <- (x `&` (W64.of_int 72057594037927935));
            x <- aux;
          }
        }
      }
      leakages <- LeakAddr([]) :: leakages;
      aux <- (b `|` x);
      b <- aux;
    } else {
      
    }
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (v.[3] `^` b);
    leakages <- LeakAddr([3]) :: leakages;
    v.[3] <- aux;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <@ sipround (v);
      v <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (v.[0] `^` b);
    leakages <- LeakAddr([0]) :: leakages;
    v.[0] <- aux;
    leakages <- LeakCond((outlen = (W64.of_int 16))) :: LeakAddr([]) :: leakages;
    if ((outlen = (W64.of_int 16))) {
      leakages <- LeakAddr([2]) :: leakages;
      aux <- (v.[2] `^` (W64.of_int 238));
      leakages <- LeakAddr([2]) :: leakages;
      v.[2] <- aux;
    } else {
      leakages <- LeakAddr([2]) :: leakages;
      aux <- (v.[2] `^` (W64.of_int 255));
      leakages <- LeakAddr([2]) :: leakages;
      v.[2] <- aux;
    }
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <@ sipround (v);
      v <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <- v.[0];
    b <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (b `^` v.[1]);
    b <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (b `^` v.[2]);
    b <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (b `^` v.[3]);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    leakages <- LeakAddr([(W64.to_uint (out + (W64.of_int (0 * 8))))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (0 * 8)))) (aux);
    leakages <- LeakCond((outlen = (W64.of_int 16))) :: LeakAddr([]) :: leakages;
    if ((outlen = (W64.of_int 16))) {
      leakages <- LeakAddr([1]) :: leakages;
      aux <- (v.[1] `^` (W64.of_int 221));
      leakages <- LeakAddr([1]) :: leakages;
      v.[1] <- aux;
      leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
      i <- 0;
      while (i < 4) {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ sipround (v);
        v <- aux_1;
        i <- i + 1;
      }
      leakages <- LeakAddr([0]) :: leakages;
      aux <- v.[0];
      b <- aux;
      leakages <- LeakAddr([1]) :: leakages;
      aux <- (b `^` v.[1]);
      b <- aux;
      leakages <- LeakAddr([2]) :: leakages;
      aux <- (b `^` v.[2]);
      b <- aux;
      leakages <- LeakAddr([3]) :: leakages;
      aux <- (b `^` v.[3]);
      b <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- b;
      leakages <- LeakAddr([(W64.to_uint (out + (W64.of_int (1 * 8))))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (1 * 8)))) (aux);
    } else {
      
    }
    return ();
  }
}.

