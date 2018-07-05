require import List Jasmin_model Int IntDiv CoreMap.


abbrev rotate24pattern = W128.of_uint 16028905388486802350658220295983399425.


module M = {
  var leakages : leakages_t
  
  proc shift (x:W128.t, count:int) : W128.t = {
    var r:W128.t;
    
    leakages <- LeakExpr([]) :: leakages;
    r <- x86_VPSLL_4u32 x (W8.of_uint count);
    return (r);
  }
  
  proc rotate (r:W128.t, count:int) : W128.t = {
    var a:W128.t;
    var b:W128.t;
    
    leakages <- LeakCond((count = 24)) :: LeakExpr([]) :: leakages;
    if ((count = 24)) {
      leakages <- LeakExpr([]) :: leakages;
      r <- x86_VPSHUFB_128 r rotate24pattern;
    } else {
      leakages <- LeakExpr([]) :: leakages;
      a <@ shift (r, count);
      leakages <- LeakExpr([]) :: leakages;
      count <- (32 - count);
      leakages <- LeakExpr([]) :: leakages;
      b <- x86_VPSRL_4u32 r (W8.of_uint count);
      leakages <- LeakExpr([]) :: leakages;
      r <- (a `^` b);
    }
    return (r);
  }
  
  proc shuffle (a:int, b:int, c:int, d:int) : int = {
    var r:int;
    
    leakages <- LeakExpr([]) :: leakages;
    r <- ((((a * 64) + (b * 16)) + (c * 4)) + d);
    return (r);
  }
  
  proc gimli_body (x:W128.t, y:W128.t, z:W128.t) : W128.t * W128.t * W128.t = {
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    var d:W128.t;
    var e:W128.t;
    var pattern:int;
    var round:int;
    var m:W32.t;
    
    leakages <- LeakFor(0,24) :: LeakExpr([]) :: leakages;
    round <- 0;
    while (24 < round) {
      leakages <- LeakExpr([]) :: leakages;
      x <@ rotate (x, 24);
      leakages <- LeakExpr([]) :: leakages;
      y <@ rotate (y, 9);
      leakages <- LeakExpr([]) :: leakages;
      a <@ shift (z, 1);
      leakages <- LeakExpr([]) :: leakages;
      b <- (y `&` z);
      leakages <- LeakExpr([]) :: leakages;
      c <@ shift (b, 2);
      leakages <- LeakExpr([]) :: leakages;
      d <- (x `^` a);
      leakages <- LeakExpr([]) :: leakages;
      e <- (d `^` c);
      leakages <- LeakExpr([]) :: leakages;
      a <- (x `|` z);
      leakages <- LeakExpr([]) :: leakages;
      b <@ shift (a, 1);
      leakages <- LeakExpr([]) :: leakages;
      c <- (y `^` x);
      leakages <- LeakExpr([]) :: leakages;
      d <- (c `^` b);
      leakages <- LeakExpr([]) :: leakages;
      a <- (x `&` y);
      leakages <- LeakExpr([]) :: leakages;
      b <@ shift (a, 3);
      leakages <- LeakExpr([]) :: leakages;
      c <- (z `^` y);
      leakages <- LeakExpr([]) :: leakages;
      x <- (c `^` b);
      leakages <- LeakExpr([]) :: leakages;
      y <- d;
      leakages <- LeakExpr([]) :: leakages;
      z <- e;
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakExpr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakExpr([]) :: leakages;
        pattern <@ shuffle (2, 3, 0, 1);
        leakages <- LeakExpr([]) :: leakages;
        x <- x86_VPSHUFD_128 x (W8.of_uint pattern);
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 2)) :: LeakExpr([]) :: leakages;
      if (((round %% 4) = 2)) {
        leakages <- LeakExpr([]) :: leakages;
        pattern <@ shuffle (1, 0, 3, 2);
        leakages <- LeakExpr([]) :: leakages;
        x <- x86_VPSHUFD_128 x (W8.of_uint pattern);
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakExpr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakExpr([]) :: leakages;
        m <- ((W32.of_uint 2654435584) `^` (W32.of_uint round));
        leakages <- LeakExpr([]) :: leakages;
        a <- x86_MOVD_32 m;
        leakages <- LeakExpr([]) :: leakages;
        x <- (x `^` a);
      } else {
        
      }
      round <- round - 1;
    }
    return (x, y, z);
  }
}.

