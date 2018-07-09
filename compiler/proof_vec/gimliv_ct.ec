require import List Jasmin_model Int IntDiv CoreMap.


abbrev rotate24pattern = W128.of_uint 16028905388486802350658220295983399425.


module M = {
  var leakages : leakages_t
  
  proc shift (x:W128.t, count:int) : W128.t = {
    var aux: W128.t;
    
    var r:W128.t;
    
    leakages <- LeakExpr([]) :: leakages;
    aux <- x86_VPSLL_4u32 x (W8.of_uint count);
    r <- aux;
    return (r);
  }
  
  proc rotate (r:W128.t, count:int) : W128.t = {
    var aux_0: int;
    var aux: W128.t;
    
    var a:W128.t;
    var b:W128.t;
    
    leakages <- LeakCond((count = 24)) :: LeakExpr([]) :: leakages;
    if ((count = 24)) {
      leakages <- LeakExpr([]) :: leakages;
      aux <- x86_VPSHUFB_128 r rotate24pattern;
      r <- aux;
    } else {
      leakages <- LeakExpr([]) :: leakages;
      aux <@ shift (r, count);
      a <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux_0 <- (32 - count);
      count <- aux_0;
      leakages <- LeakExpr([]) :: leakages;
      aux <- x86_VPSRL_4u32 r (W8.of_uint count);
      b <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (a `^` b);
      r <- aux;
    }
    return (r);
  }
  
  proc shuffle (a:int, b:int, c:int, d:int) : int = {
    var aux: int;
    
    var r:int;
    
    leakages <- LeakExpr([]) :: leakages;
    aux <- ((((a * 64) + (b * 16)) + (c * 4)) + d);
    r <- aux;
    return (r);
  }
  
  proc gimli_body (x:W128.t, y:W128.t, z:W128.t) : W128.t * W128.t * W128.t = {
    var aux_0: int;
    var aux_1: W32.t;
    var aux: W128.t;
    
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
      aux <@ rotate (x, 24);
      x <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <@ rotate (y, 9);
      y <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <@ shift (z, 1);
      a <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (y `&` z);
      b <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <@ shift (b, 2);
      c <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (x `^` a);
      d <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (d `^` c);
      e <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (x `|` z);
      a <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <@ shift (a, 1);
      b <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (y `^` x);
      c <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (c `^` b);
      d <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (x `&` y);
      a <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <@ shift (a, 3);
      b <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (z `^` y);
      c <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- (c `^` b);
      x <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- d;
      y <- aux;
      leakages <- LeakExpr([]) :: leakages;
      aux <- e;
      z <- aux;
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakExpr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakExpr([]) :: leakages;
        aux_0 <@ shuffle (2, 3, 0, 1);
        pattern <- aux_0;
        leakages <- LeakExpr([]) :: leakages;
        aux <- x86_VPSHUFD_128 x (W8.of_uint pattern);
        x <- aux;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 2)) :: LeakExpr([]) :: leakages;
      if (((round %% 4) = 2)) {
        leakages <- LeakExpr([]) :: leakages;
        aux_0 <@ shuffle (1, 0, 3, 2);
        pattern <- aux_0;
        leakages <- LeakExpr([]) :: leakages;
        aux <- x86_VPSHUFD_128 x (W8.of_uint pattern);
        x <- aux;
      } else {
        
      }
      leakages <- LeakCond(((round %% 4) = 0)) :: LeakExpr([]) :: leakages;
      if (((round %% 4) = 0)) {
        leakages <- LeakExpr([]) :: leakages;
        aux_1 <- ((W32.of_uint 2654435584) `^` (W32.of_uint round));
        m <- aux_1;
        leakages <- LeakExpr([]) :: leakages;
        aux <- x86_MOVD_32 m;
        a <- aux;
        leakages <- LeakExpr([]) :: leakages;
        aux <- (x `^` a);
        x <- aux;
      } else {
        
      }
      round <- (round - 1);
    }
    return (x, y, z);
  }
}.

