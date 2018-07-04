require import List Jasmin_model Int IntDiv CoreMap.

abbrev rotate24pattern = W128.of_uint 16028905388486802350658220295983399425.


module M = {
  proc shift (x:W128.t, count:int) : W128.t = {
    var r:W128.t;
    
    r <- x86_VPSLL_4u32 x (W8.of_uint count);
    return (r);
  }
  
  proc rotate1 (r:W128.t, count:int) : W128.t = {
    var a:W128.t;
    var b:W128.t;
    
    a <@ shift (r, count);
    count <- (32 - count);
    b <- x86_VPSRL_4u32 r (W8.of_uint count);
    r <- (a `^` b);
    return (r);
  }
  
  proc shuffle (a:int, b:int, c:int, d:int) : int = {
    var r:int;
    
    r <- ((((a * 64) + (b * 16)) + (c * 4)) + d);
    return (r);
  }
  
  proc gimli_body1 (x:W128.t, y:W128.t, z:W128.t) : W128.t * W128.t * W128.t = {
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W128.t;
    var e:W128.t;
    var pattern:int;
    var round:int;
    var m:W32.t;
    
    round <- 0;
    while (24 < round) {
      x <@ rotate1 (x, 24);
      y <@ rotate1 (y, 9);
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
        pattern <@ shuffle (2, 3, 0, 1);
        x <- x86_VPSHUFD_128 x (W8.of_uint pattern);
      } else {
        
      }
      if (((round %% 4) = 2)) {
        pattern <@ shuffle (1, 0, 3, 2);
        x <- x86_VPSHUFD_128 x (W8.of_uint pattern);
      } else {
        
      }
      if (((round %% 4) = 0)) {
        m <- ((W32.of_uint 2654435584) `^` (W32.of_uint round));
        a <- x86_MOVD_32 m;
        x <- (x `^` a);
      } else {
        
      }
      round <- round - 1;
    }
    return (x, y, z);
  }
}.

