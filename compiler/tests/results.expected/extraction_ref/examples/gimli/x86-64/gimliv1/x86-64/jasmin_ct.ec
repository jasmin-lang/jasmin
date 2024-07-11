require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc shift (x:W128.t, count:int) : W128.t = {
    var aux: W128.t;
    
    var r:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSLL_4u32 x (W8.of_int count);
    r <- aux;
    return (r);
  }
  
  proc rotate (r:W128.t, count:int) : W128.t = {
    var aux_0: int;
    var aux: W128.t;
    
    var a:W128.t;
    var b:W128.t;
    var rotate24pattern:W128.t;
    
    leakages <- LeakCond((false /\ (count = 24))) :: LeakAddr([]) :: leakages;
    if ((false /\ (count = 24))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W128.of_int (1 %% 2^8 + 2^8 * (2 %% 2^8 + 2^8 * (3 %% 2^8 + 2^8 * (0 %% 2^8 + 2^8 * (5 %% 2^8 + 2^8 * (6 %% 2^8 + 2^8 * (7 %% 2^8 + 2^8 * (4 %% 2^8 + 2^8 * (9 %% 2^8 + 2^8 * (10 %% 2^8 + 2^8 * (11 %% 2^8 + 2^8 * (8 %% 2^8 + 2^8 * (13 %% 2^8 + 2^8 * (14 %% 2^8 + 2^8 * (15 %% 2^8 + 2^8 * 12))))))))))))))));
      rotate24pattern <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- VPSHUFB_128 r rotate24pattern;
      r <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ shift (r, count);
      a <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (32 - count);
      count <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- VPSRL_4u32 r (W8.of_int count);
      b <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (a `^` b);
      r <- aux;
    }
    return (r);
  }
  
  proc gimli_body (x:W128.t, y:W128.t, z:W128.t) : W128.t * W128.t * W128.t = {
    var aux: int;
    var aux_1: W32.t;
    var aux_0: W128.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W128.t;
    var e:W128.t;
    var round:int;
    var m:W32.t;
    
    leakages <- LeakFor(24,0) :: LeakAddr([]) :: leakages;
    round <- 24;
    while (0 < round) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ rotate (x, 24);
      x <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ rotate (y, 9);
      y <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ shift (z, 1);
      a <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (y `&` z);
      b <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ shift (b, 2);
      c <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (x `^` a);
      d <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (d `^` c);
      e <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (x `|` z);
      a <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ shift (a, 1);
      b <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (y `^` x);
      c <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (c `^` b);
      d <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (x `&` y);
      a <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ shift (a, 3);
      b <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (z `^` y);
      c <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (c `^` b);
      x <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- d;
      y <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- e;
      z <- aux_0;
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- VPSHUFD_128 x (W8.of_int (1 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 2))));
        x <- aux_0;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 2)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 2)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- VPSHUFD_128 x (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
        x <- aux_0;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakAddr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- ((W32.of_int 2654435584) + (W32.of_int round));
        m <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (zeroextu128 m);
        a <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (x `^` a);
        x <- aux_0;
      } else {
        
      }
      round <- round - 1;
    }
    return (x, y, z);
  }
  
  proc gimli (io:W64.t) : unit = {
    var aux_1: W128.t;
    var aux_0: W128.t;
    var aux: W128.t;
    
    var x:W128.t;
    var y:W128.t;
    var z:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (io + (W64.of_int (16 * 0))))]) :: leakages;
    aux_1 <- (loadW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 0)))));
    x <- aux_1;
    leakages <- LeakAddr([(W64.to_uint (io + (W64.of_int (16 * 1))))]) :: leakages;
    aux_1 <- (loadW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 1)))));
    y <- aux_1;
    leakages <- LeakAddr([(W64.to_uint (io + (W64.of_int (16 * 2))))]) :: leakages;
    aux_1 <- (loadW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 2)))));
    z <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0, aux) <@ gimli_body (x, y, z);
    x <- aux_1;
    y <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x;
    leakages <- LeakAddr([(W64.to_uint (io + (W64.of_int (16 * 0))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 0)))) (aux_1);
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- y;
    leakages <- LeakAddr([(W64.to_uint (io + (W64.of_int (16 * 1))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 1)))) (aux_1);
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- z;
    leakages <- LeakAddr([(W64.to_uint (io + (W64.of_int (16 * 2))))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 2)))) (aux_1);
    return ();
  }
}.

