require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc shift (x:W128.t, count:int) : W128.t = {
    
    var r:W128.t;
    
    r <- VPSLL_4u32 x (W8.of_int count);
    return (r);
  }
  
  proc rotate (r:W128.t, count:int) : W128.t = {
    
    var a:W128.t;
    var b:W128.t;
    var rotate24pattern:W128.t;
    
    if ((false /\ (count = 24))) {
      rotate24pattern <- (W128.of_int (1 %% 2^8 + 2^8 * (2 %% 2^8 + 2^8 * (3 %% 2^8 + 2^8 * (0 %% 2^8 + 2^8 * (5 %% 2^8 + 2^8 * (6 %% 2^8 + 2^8 * (7 %% 2^8 + 2^8 * (4 %% 2^8 + 2^8 * (9 %% 2^8 + 2^8 * (10 %% 2^8 + 2^8 * (11 %% 2^8 + 2^8 * (8 %% 2^8 + 2^8 * (13 %% 2^8 + 2^8 * (14 %% 2^8 + 2^8 * (15 %% 2^8 + 2^8 * 12))))))))))))))));
      r <- VPSHUFB_128 r rotate24pattern;
    } else {
      a <@ shift (r, count);
      count <- (32 - count);
      b <- VPSRL_4u32 r (W8.of_int count);
      r <- (a `^` b);
    }
    return (r);
  }
  
  proc gimli_body (x:W128.t, y:W128.t, z:W128.t) : W128.t * W128.t * W128.t = {
    var aux: int;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W128.t;
    var e:W128.t;
    var round:int;
    var m:W32.t;
    
    round <- 24;
    while (0 < round) {
      x <@ rotate (x, 24);
      y <@ rotate (y, 9);
      a <@ shift (z, 1);
      b <- (y `&` z);
      c <@ shift (b, 2);
      d <- (x `^` a);
      e <- (d `^` c);
      a <- (x `|` z);
      b <@ shift (a, 1);
      c <- (y `^` x);
      d <- (c `^` b);
      a <- (x `&` y);
      b <@ shift (a, 3);
      c <- (z `^` y);
      x <- (c `^` b);
      y <- d;
      z <- e;
      if (((round %% 4) = 0)) {
        x <- VPSHUFD_128 x (W8.of_int (1 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 2))));
      } else {
        
      }
      if (((round %% 4) = 2)) {
        x <- VPSHUFD_128 x (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
      } else {
        
      }
      if (((round %% 4) = 0)) {
        m <- ((W32.of_int 2654435584) + (W32.of_int round));
        a <- (zeroextu128 m);
        x <- (x `^` a);
      } else {
        
      }
      round <- round - 1;
    }
    return (x, y, z);
  }
  
  proc gimli (io:W64.t) : unit = {
    
    var x:W128.t;
    var y:W128.t;
    var z:W128.t;
    
    x <- (loadW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 0)))));
    y <- (loadW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 1)))));
    z <- (loadW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 2)))));
    (x, y, z) <@ gimli_body (x, y, z);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 0)))) (x);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 1)))) (y);
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (io + (W64.of_int (16 * 2)))) (z);
    return ();
  }
}.

