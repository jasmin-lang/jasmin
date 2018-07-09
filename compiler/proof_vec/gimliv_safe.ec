require import List Jasmin_model Int IntDiv CoreMap.


abbrev rotate24pattern = W128.of_uint 16028905388486802350658220295983399425.


module M = {
  var safe : bool
  
  proc shift (x:W128.t, count:int) : W128.t = {
    var aux: W128.t;
    
    var r:W128.t option;
    
    aux <- x86_VPSLL_4u32 x (W8.of_uint count);
    r <- Some aux;
    return ((oget r));
  }
  
  proc rotate (r:W128.t, count:int) : W128.t = {
    var aux_0: int;
    var aux: W128.t;
    
    var a:W128.t option;
    var b:W128.t option;
    
    if ((count = 24)) {
      aux <- x86_VPSHUFB_128 r rotate24pattern;
      r <- aux;
    } else {
      aux <@ shift (r, count);
      a <- Some aux;
      aux_0 <- (32 - count);
      count <- aux_0;
      aux <- x86_VPSRL_4u32 r (W8.of_uint count);
      b <- Some aux;
      safe <- safe /\ is_init b/\ is_init a;
      aux <- ((oget a) `^` (oget b));
      r <- aux;
    }
    return (r);
  }
  
  proc shuffle (a:int, b:int, c:int, d:int) : int = {
    var aux: int;
    
    var r:int option;
    
    aux <- ((((a * 64) + (b * 16)) + (c * 4)) + d);
    r <- Some aux;
    return ((oget r));
  }
  
  proc gimli_body (x:W128.t, y:W128.t, z:W128.t) : W128.t * W128.t * W128.t = {
    var aux_0: int;
    var aux_1: W32.t;
    var aux: W128.t;
    
    var a:W128.t option;
    var b:W128.t option;
    var c:W128.t option;
    var d:W128.t option;
    var e:W128.t option;
    var pattern:int option;
    var round:int option;
    var m:W32.t option;
    
    round <- Some 0;
    while (24 < (oget round)) {
      aux <@ rotate (x, 24);
      x <- aux;
      aux <@ rotate (y, 9);
      y <- aux;
      aux <@ shift (z, 1);
      a <- Some aux;
      aux <- (y `&` z);
      b <- Some aux;
      safe <- safe /\ is_init b;
      aux <@ shift ((oget b), 2);
      c <- Some aux;
      safe <- safe /\ is_init a;
      aux <- (x `^` (oget a));
      d <- Some aux;
      safe <- safe /\ is_init c/\ is_init d;
      aux <- ((oget d) `^` (oget c));
      e <- Some aux;
      aux <- (x `|` z);
      a <- Some aux;
      safe <- safe /\ is_init a;
      aux <@ shift ((oget a), 1);
      b <- Some aux;
      aux <- (y `^` x);
      c <- Some aux;
      safe <- safe /\ is_init b/\ is_init c;
      aux <- ((oget c) `^` (oget b));
      d <- Some aux;
      aux <- (x `&` y);
      a <- Some aux;
      safe <- safe /\ is_init a;
      aux <@ shift ((oget a), 3);
      b <- Some aux;
      aux <- (z `^` y);
      c <- Some aux;
      safe <- safe /\ is_init b/\ is_init c;
      aux <- ((oget c) `^` (oget b));
      x <- aux;
      safe <- safe /\ is_init d;
      aux <- (oget d);
      y <- aux;
      safe <- safe /\ is_init e;
      aux <- (oget e);
      z <- aux;
      safe <- safe /\ is_init round;
      if ((((oget round) %% 4) = 0)) {
        aux_0 <@ shuffle (2, 3, 0, 1);
        pattern <- Some aux_0;
        safe <- safe /\ is_init pattern;
        aux <- x86_VPSHUFD_128 x (W8.of_uint (oget pattern));
        x <- aux;
      } else {
        
      }
      safe <- safe /\ is_init round;
      if ((((oget round) %% 4) = 2)) {
        aux_0 <@ shuffle (1, 0, 3, 2);
        pattern <- Some aux_0;
        safe <- safe /\ is_init pattern;
        aux <- x86_VPSHUFD_128 x (W8.of_uint (oget pattern));
        x <- aux;
      } else {
        
      }
      safe <- safe /\ is_init round;
      if ((((oget round) %% 4) = 0)) {
        safe <- safe /\ is_init round;
        aux_1 <- ((W32.of_uint 2654435584) `^` (W32.of_uint (oget round)));
        m <- Some aux_1;
        safe <- safe /\ is_init m;
        aux <- x86_MOVD_32 (oget m);
        a <- Some aux;
        safe <- safe /\ is_init a;
        aux <- (x `^` (oget a));
        x <- aux;
      } else {
        
      }
      round <- Some ((oget round) - 1);
    }
    return (x, y, z);
  }
}.

