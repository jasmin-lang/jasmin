require import List Jasmin_model Int IntDiv CoreMap.


abbrev zero_u128 = W128.of_uint 0.


abbrev five_u128 = W128.of_uint 92233720368547758085.


abbrev bit25_u128 = W128.of_uint 309485009821345068741558272.


abbrev mask26_u128 = W128.of_uint 1237940020838636201256681471.


module M = {
  var safe : bool
  
  proc add (x:W64.t Array5.t, y:W64.t Array5.t) : W64.t Array5.t = {
    var aux: W64.t;
    
    var i:int option;
    
    i <- Some 0;
    while ((oget i) < 5) {
      safe <- safe /\ in_bound (oget i) 5/\ is_init y.[(oget i)]/\
              is_init i/\ in_bound (oget i) 5/\ is_init x.[(oget i)]/\
              is_init i;
      aux <- ((oget x.[(oget i)]) + (oget y.[(oget i)]));
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      x.[(oget i)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    return (x);
  }
  
  proc add_carry (x:W64.t Array5.t, y:W64.t Array5.t) : W64.t Array5.t = {
    var aux: W64.t;
    
    var i:int option;
    var c:W64.t option;
    
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- ((oget x.[0]) + (oget y.[0]));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    i <- Some 0;
    while ((oget i) < 4) {
      safe <- safe /\ in_bound (oget i) 5/\ is_init x.[(oget i)]/\ is_init i;
      aux <- (oget x.[(oget i)]);
      c <- Some aux;
      safe <- safe /\ is_init c;
      aux <- ((oget c) `>>` (W8.of_uint 26));
      c <- Some aux;
      safe <- safe /\ in_bound (oget i) 5/\ is_init x.[(oget i)]/\ is_init i;
      aux <- ((oget x.[(oget i)]) `&` (W64.of_uint 67108863));
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      x.[(oget i)] <- Some aux;
      safe <- safe /\ in_bound ((oget i) + 1) 5/\
              is_init y.[((oget i) + 1)]/\ is_init i/\
              in_bound ((oget i) + 1) 5/\ is_init x.[((oget i) + 1)]/\
              is_init i;
      aux <- ((oget x.[((oget i) + 1)]) + (oget y.[((oget i) + 1)]));
      safe <- safe /\ in_bound ((oget i) + 1) 5/\ is_init i;
      x.[((oget i) + 1)] <- Some aux;
      safe <- safe /\ is_init c/\ in_bound ((oget i) + 1) 5/\
              is_init x.[((oget i) + 1)]/\ is_init i;
      aux <- ((oget x.[((oget i) + 1)]) + (oget c));
      safe <- safe /\ in_bound ((oget i) + 1) 5/\ is_init i;
      x.[((oget i) + 1)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    return (x);
  }
  
  proc add_u128 (x:W128.t Array5.t, y:W128.t Array5.t) : W128.t Array5.t = {
    var aux: W128.t;
    
    var i:int option;
    
    i <- Some 0;
    while ((oget i) < 5) {
      safe <- safe /\ in_bound (oget i) 5/\ is_init y.[(oget i)]/\
              is_init i/\ in_bound (oget i) 5/\ is_init x.[(oget i)]/\
              is_init i;
      aux <- x86_VPADD_2u64 (oget x.[(oget i)]) (oget y.[(oget i)]);
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      x.[(oget i)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    return (x);
  }
  
  proc hadd_u128 (x:W128.t Array5.t) : W64.t Array5.t = {
    var aux: W64.t;
    var aux_0: W64.t Array5.t;
    
    var h:W64.t option Array5.t;
    var i:int option;
    var t:W64.t option Array5.t;
    h <- Array5.init None;
    t <- Array5.init None;
    i <- Some 0;
    while ((oget i) < 5) {
      safe <- safe /\ in_bound (oget i) 5/\ is_init x.[(oget i)]/\ is_init i;
      aux <- x86_VPEXTR_64 (oget x.[(oget i)]) (W8.of_uint 1);
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      t.[(oget i)] <- Some aux;
      safe <- safe /\ in_bound (oget i) 5/\ is_init x.[(oget i)]/\ is_init i;
      aux <- x86_VPEXTR_64 (oget x.[(oget i)]) (W8.of_uint 0);
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      h.[(oget i)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    aux_0 <@ add_carry ((oget h), (oget t));
    h <- aux_0;
    return ((oget h));
  }
  
  proc freeze (x:W64.t Array5.t) : W64.t Array5.t = {
    var aux_0: W64.t;
    var aux: W64.t Array5.t;
    
    var ox:W64.t option Array5.t;
    var mp:W64.t option Array5.t;
    var n:W64.t option;
    mp <- Array5.init None;
    ox <- Array5.init None;
    aux <- x;
    ox <- aux;
    aux_0 <- (W64.of_uint 5);
    safe <- safe /\ in_bound 0 5;
    mp.[0] <- Some aux_0;
    aux_0 <- (W64.of_uint 0);
    safe <- safe /\ in_bound 1 5;
    mp.[1] <- Some aux_0;
    aux_0 <- (W64.of_uint 0);
    safe <- safe /\ in_bound 2 5;
    mp.[2] <- Some aux_0;
    aux_0 <- (W64.of_uint 0);
    safe <- safe /\ in_bound 3 5;
    mp.[3] <- Some aux_0;
    aux_0 <- (W64.of_uint 67108864);
    safe <- safe /\ in_bound 4 5;
    mp.[4] <- Some aux_0;
    aux <@ add_carry (x, (oget mp));
    x <- aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux_0 <- (oget x.[4]);
    n <- Some aux_0;
    safe <- safe /\ is_init n;
    aux_0 <- ((oget n) `>>` (W8.of_uint 26));
    n <- Some aux_0;
    safe <- safe /\ is_init n;
    aux_0 <- ((oget n) `&` (W64.of_uint 1));
    n <- Some aux_0;
    safe <- safe /\ is_init n;
    aux_0 <- (- (oget n));
    n <- Some aux_0;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0]/\ in_bound 0 5/\
            is_init ox.[0];
    aux_0 <- ((oget ox.[0]) `^` (oget x.[0]));
    safe <- safe /\ in_bound 0 5;
    ox.[0] <- Some aux_0;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1]/\ in_bound 1 5/\
            is_init ox.[1];
    aux_0 <- ((oget ox.[1]) `^` (oget x.[1]));
    safe <- safe /\ in_bound 1 5;
    ox.[1] <- Some aux_0;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2]/\ in_bound 2 5/\
            is_init ox.[2];
    aux_0 <- ((oget ox.[2]) `^` (oget x.[2]));
    safe <- safe /\ in_bound 2 5;
    ox.[2] <- Some aux_0;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3]/\ in_bound 3 5/\
            is_init ox.[3];
    aux_0 <- ((oget ox.[3]) `^` (oget x.[3]));
    safe <- safe /\ in_bound 3 5;
    ox.[3] <- Some aux_0;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4]/\ in_bound 4 5/\
            is_init ox.[4];
    aux_0 <- ((oget ox.[4]) `^` (oget x.[4]));
    safe <- safe /\ in_bound 4 5;
    ox.[4] <- Some aux_0;
    safe <- safe /\ is_init n/\ in_bound 0 5/\ is_init ox.[0];
    aux_0 <- ((oget ox.[0]) `&` (oget n));
    safe <- safe /\ in_bound 0 5;
    ox.[0] <- Some aux_0;
    safe <- safe /\ is_init n/\ in_bound 1 5/\ is_init ox.[1];
    aux_0 <- ((oget ox.[1]) `&` (oget n));
    safe <- safe /\ in_bound 1 5;
    ox.[1] <- Some aux_0;
    safe <- safe /\ is_init n/\ in_bound 2 5/\ is_init ox.[2];
    aux_0 <- ((oget ox.[2]) `&` (oget n));
    safe <- safe /\ in_bound 2 5;
    ox.[2] <- Some aux_0;
    safe <- safe /\ is_init n/\ in_bound 3 5/\ is_init ox.[3];
    aux_0 <- ((oget ox.[3]) `&` (oget n));
    safe <- safe /\ in_bound 3 5;
    ox.[3] <- Some aux_0;
    safe <- safe /\ is_init n/\ in_bound 4 5/\ is_init ox.[4];
    aux_0 <- ((oget ox.[4]) `&` (oget n));
    safe <- safe /\ in_bound 4 5;
    ox.[4] <- Some aux_0;
    safe <- safe /\ in_bound 0 5/\ is_init ox.[0]/\ in_bound 0 5/\
            is_init x.[0];
    aux_0 <- ((oget x.[0]) `^` (oget ox.[0]));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux_0;
    safe <- safe /\ in_bound 1 5/\ is_init ox.[1]/\ in_bound 1 5/\
            is_init x.[1];
    aux_0 <- ((oget x.[1]) `^` (oget ox.[1]));
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux_0;
    safe <- safe /\ in_bound 2 5/\ is_init ox.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux_0 <- ((oget x.[2]) `^` (oget ox.[2]));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux_0;
    safe <- safe /\ in_bound 3 5/\ is_init ox.[3]/\ in_bound 3 5/\
            is_init x.[3];
    aux_0 <- ((oget x.[3]) `^` (oget ox.[3]));
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux_0;
    safe <- safe /\ in_bound 4 5/\ is_init ox.[4]/\ in_bound 4 5/\
            is_init x.[4];
    aux_0 <- ((oget x.[4]) `^` (oget ox.[4]));
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux_0;
    return (x);
  }
  
  proc unpack (m:W64.t) : W64.t Array5.t = {
    var aux: W64.t;
    
    var x:W64.t option Array5.t;
    var m0:W64.t option;
    var m1:W64.t option;
    var t:W64.t option;
    x <- Array5.init None;
    safe <- safe /\ is_valid Glob.mem (m + (W64.of_uint (8 * 0))) W64;
    aux <- (loadW64 Glob.mem (m + (W64.of_uint (8 * 0))));
    m0 <- Some aux;
    safe <- safe /\ is_valid Glob.mem (m + (W64.of_uint (8 * 1))) W64;
    aux <- (loadW64 Glob.mem (m + (W64.of_uint (8 * 1))));
    m1 <- Some aux;
    safe <- safe /\ is_init m0;
    aux <- (oget m0);
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- ((oget x.[0]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ is_init m0;
    aux <- ((oget m0) `>>` (W8.of_uint 26));
    m0 <- Some aux;
    safe <- safe /\ is_init m0;
    aux <- (oget m0);
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- ((oget x.[1]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ is_init m0;
    aux <- ((oget m0) `>>` (W8.of_uint 26));
    m0 <- Some aux;
    safe <- safe /\ is_init m0;
    aux <- (oget m0);
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ is_init m1;
    aux <- (oget m1);
    t <- Some aux;
    safe <- safe /\ is_init t;
    aux <- ((oget t) `<<` (W8.of_uint 12));
    t <- Some aux;
    safe <- safe /\ is_init t/\ in_bound 2 5/\ is_init x.[2];
    aux <- ((oget x.[2]) `|` (oget t));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- ((oget x.[2]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ is_init m1;
    aux <- ((oget m1) `>>` (W8.of_uint 14));
    m1 <- Some aux;
    safe <- safe /\ is_init m1;
    aux <- (oget m1);
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- ((oget x.[3]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ is_init m1;
    aux <- ((oget m1) `>>` (W8.of_uint 26));
    m1 <- Some aux;
    safe <- safe /\ is_init m1;
    aux <- (oget m1);
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    return ((oget x));
  }
  
  proc mulmod_12 (x:W64.t Array5.t, y:W64.t Array5.t, yx5:W64.t Array4.t) : 
  W64.t Array5.t = {
    var aux: W64.t;
    
    var t:W64.t option Array5.t;
    var z:W64.t option Array3.t;
    t <- Array5.init None;
    z <- Array3.init None;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- ((oget t.[0]) * (oget y.[0]));
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- ((oget t.[1]) * (oget y.[1]));
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- ((oget t.[2]) * (oget y.[2]));
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- ((oget t.[3]) * (oget y.[3]));
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init y.[4]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- ((oget t.[4]) * (oget y.[4]));
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- (oget x.[1]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget y.[0]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- (oget x.[1]);
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 1 3/\
            is_init z.[1];
    aux <- ((oget z.[1]) * (oget y.[1]));
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- (oget x.[1]);
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 2 3/\
            is_init z.[2];
    aux <- ((oget z.[2]) * (oget y.[2]));
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- ((oget t.[1]) + (oget z.[0]));
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 3/\ is_init z.[1]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- ((oget t.[2]) + (oget z.[1]));
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 2 3/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- ((oget t.[3]) + (oget z.[2]));
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- (oget x.[1]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget y.[3]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 1 3/\
            is_init z.[1];
    aux <- ((oget z.[1]) * (oget y.[0]));
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 2 3/\
            is_init z.[2];
    aux <- ((oget z.[2]) * (oget y.[1]));
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- ((oget t.[4]) + (oget z.[0]));
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 1 3/\ is_init z.[1]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- ((oget t.[2]) + (oget z.[1]));
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 2 3/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- ((oget t.[3]) + (oget z.[2]));
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget y.[2]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 1 3/\
            is_init z.[1];
    aux <- ((oget z.[1]) * (oget y.[0]));
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 2 3/\
            is_init z.[2];
    aux <- ((oget z.[2]) * (oget y.[1]));
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- ((oget t.[4]) + (oget z.[0]));
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- (oget x.[4]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget y.[0]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 3/\ is_init z.[1]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- ((oget t.[3]) + (oget z.[1]));
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 2 3/\ is_init z.[2]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- ((oget t.[4]) + (oget z.[2]));
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- ((oget t.[4]) + (oget z.[0]));
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- (oget x.[4]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 4/\ is_init yx5.[0]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget yx5.[0]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 1 3/\
            is_init z.[1];
    aux <- ((oget z.[1]) * (oget yx5.[1]));
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- (oget x.[4]);
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 2 3/\
            is_init z.[2];
    aux <- ((oget z.[2]) * (oget yx5.[1]));
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- ((oget t.[0]) + (oget z.[0]));
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 1 3/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- ((oget t.[0]) + (oget z.[1]));
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 3/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- ((oget t.[1]) + (oget z.[2]));
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- (oget x.[4]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget yx5.[2]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 1 3/\
            is_init z.[1];
    aux <- ((oget z.[1]) * (oget yx5.[2]));
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 2 3/\
            is_init z.[2];
    aux <- ((oget z.[2]) * (oget yx5.[2]));
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- ((oget t.[2]) + (oget z.[0]));
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 1 3/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- ((oget t.[0]) + (oget z.[1]));
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 3/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- ((oget t.[1]) + (oget z.[2]));
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- (oget x.[1]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget yx5.[3]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 1 3/\
            is_init z.[1];
    aux <- ((oget z.[1]) * (oget yx5.[3]));
    safe <- safe /\ in_bound 1 3;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 2 3/\
            is_init z.[2];
    aux <- ((oget z.[2]) * (oget yx5.[3]));
    safe <- safe /\ in_bound 2 3;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init t.[0];
    aux <- (oget t.[0]);
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- ((oget x.[0]) + (oget z.[0]));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- (oget x.[4]);
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 0 3/\
            is_init z.[0];
    aux <- ((oget z.[0]) * (oget yx5.[3]));
    safe <- safe /\ in_bound 0 3;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init t.[1];
    aux <- (oget t.[1]);
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 1 3/\ is_init z.[1]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- ((oget x.[1]) + (oget z.[1]));
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init t.[2];
    aux <- (oget t.[2]);
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 2 3/\ is_init z.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- ((oget x.[2]) + (oget z.[2]));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init t.[3];
    aux <- (oget t.[3]);
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- ((oget x.[3]) + (oget z.[0]));
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init t.[4];
    aux <- (oget t.[4]);
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    return (x);
  }
  
  proc carry_reduce (x:W64.t Array5.t) : W64.t Array5.t = {
    var aux: W64.t;
    
    var z:W64.t option Array2.t;
    z <- Array2.init None;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0];
    aux <- ((oget z.[0]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1];
    aux <- ((oget z.[1]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- ((oget x.[0]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- ((oget x.[3]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- ((oget x.[1]) + (oget z.[0]));
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- ((oget x.[4]) + (oget z.[1]));
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- (oget x.[1]);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0];
    aux <- ((oget z.[0]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- (oget x.[4]);
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1];
    aux <- ((oget z.[1]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1];
    aux <- ((oget z.[1]) `&` (W64.of_uint 4294967295));
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1];
    aux <- ((oget z.[1]) * (W64.of_uint 5));
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- ((oget x.[1]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- ((oget x.[4]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- ((oget x.[2]) + (oget z.[0]));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- ((oget x.[0]) + (oget z.[1]));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0];
    aux <- ((oget z.[0]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1];
    aux <- ((oget z.[1]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- ((oget x.[2]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- ((oget x.[0]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- ((oget x.[3]) + (oget z.[0]));
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- ((oget x.[1]) + (oget z.[1]));
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0];
    aux <- ((oget z.[0]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- ((oget x.[3]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- ((oget x.[4]) + (oget z.[0]));
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    return (x);
  }
  
  proc unpack_u26x5x2_to_u26x5x2 (s:W64.t Array5.t, t:W64.t Array5.t) : 
  W128.t Array5.t = {
    var aux: W128.t;
    
    var r:W128.t option Array5.t;
    var i:int option;
    r <- Array5.init None;
    i <- Some 0;
    while ((oget i) < 5) {
      aux <- zero_u128;
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      r.[(oget i)] <- Some aux;
      safe <- safe /\ in_bound (oget i) 5/\ is_init s.[(oget i)]/\
              is_init i/\ in_bound (oget i) 5/\ is_init r.[(oget i)]/\
              is_init i;
      aux <- x86_VPINSR_2u64 (oget r.[(oget i)]) (oget s.[(oget i)])
      (W8.of_uint 0);
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      r.[(oget i)] <- Some aux;
      safe <- safe /\ in_bound (oget i) 5/\ is_init t.[(oget i)]/\
              is_init i/\ in_bound (oget i) 5/\ is_init r.[(oget i)]/\
              is_init i;
      aux <- x86_VPINSR_2u64 (oget r.[(oget i)]) (oget t.[(oget i)])
      (W8.of_uint 1);
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      r.[(oget i)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    return ((oget r));
  }
  
  proc unpack_u128x2_to_u26x5x2 (m:W64.t) : W128.t Array5.t = {
    var aux: W128.t;
    
    var r:W128.t option Array5.t;
    var s128:W128.t option;
    var t128:W128.t option;
    var t1:W128.t option;
    var t2:W128.t option;
    var t3:W128.t option;
    r <- Array5.init None;
    safe <- safe /\ is_valid Glob.mem (m + (W64.of_uint (8 * 0))) W64;
    aux <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 0))));
    s128 <- Some aux;
    safe <- safe /\ is_valid Glob.mem (m + (W64.of_uint (8 * 2))) W64;
    aux <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 2))));
    t128 <- Some aux;
    safe <- safe /\ is_init t128/\ is_init s128;
    aux <- x86_VPUNPCKL_2u64 (oget s128) (oget t128);
    t1 <- Some aux;
    safe <- safe /\ is_valid Glob.mem (m + (W64.of_uint (8 * 1))) W64;
    aux <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 1))));
    s128 <- Some aux;
    safe <- safe /\ is_valid Glob.mem (m + (W64.of_uint (8 * 3))) W64;
    aux <- x86_MOVD_64 (loadW64 Glob.mem (m + (W64.of_uint (8 * 3))));
    t128 <- Some aux;
    safe <- safe /\ is_init t128/\ is_init s128;
    aux <- x86_VPUNPCKL_2u64 (oget s128) (oget t128);
    t2 <- Some aux;
    safe <- safe /\ is_init t2;
    aux <- x86_VPSLL_2u64 (oget t2) (W8.of_uint 12);
    t3 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- x86_VPAND_128 (oget t1) mask26_u128;
    safe <- safe /\ in_bound 0 5;
    r.[0] <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- x86_VPSRL_2u64 (oget t1) (W8.of_uint 26);
    t1 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- x86_VPAND_128 (oget t1) mask26_u128;
    safe <- safe /\ in_bound 1 5;
    r.[1] <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- x86_VPSRL_2u64 (oget t1) (W8.of_uint 26);
    t1 <- Some aux;
    safe <- safe /\ is_init t3/\ is_init t1;
    aux <- x86_VPOR_128 (oget t1) (oget t3);
    t1 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- x86_VPAND_128 (oget t1) mask26_u128;
    safe <- safe /\ in_bound 2 5;
    r.[2] <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- x86_VPSRL_2u64 (oget t1) (W8.of_uint 26);
    t1 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- x86_VPAND_128 (oget t1) mask26_u128;
    safe <- safe /\ in_bound 3 5;
    r.[3] <- Some aux;
    safe <- safe /\ is_init t2;
    aux <- x86_VPSRL_2u64 (oget t2) (W8.of_uint 40);
    safe <- safe /\ in_bound 4 5;
    r.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init r.[4];
    aux <- x86_VPOR_128 (oget r.[4]) bit25_u128;
    safe <- safe /\ in_bound 4 5;
    r.[4] <- Some aux;
    return ((oget r));
  }
  
  proc mulmod_u128 (x:W128.t Array5.t, y:W128.t Array5.t, yx5:W128.t Array4.t) : 
  W128.t Array5.t = {
    var aux: W128.t;
    
    var t:W128.t option Array5.t;
    var z:W128.t option Array5.t;
    t <- Array5.init None;
    z <- Array5.init None;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[0]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[1]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[2]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[3]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init y.[4]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[4]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[0]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[1]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[2]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[3]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[0]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[0]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[1]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[2]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[3]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[4]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[1]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[2]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget y.[0]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget y.[1]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget y.[0]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[0]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[1]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[2]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[3]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[4]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 0 4/\ is_init yx5.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[0]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[1]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[1]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget yx5.[2]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[2]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[0]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[2]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[1]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[4]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[3]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[2]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget yx5.[3]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget yx5.[3]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[3]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[3]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[0]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[1]);
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[2]);
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[3]);
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[4]);
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init t.[4];
    aux <- (oget t.[4]);
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    return (x);
  }
  
  proc mulmod_u128_prefetch (in_0:W64.t, x:W128.t Array5.t,
                             y:W128.t Array5.t, yx5:W128.t Array4.t) : 
  W128.t Array5.t * W128.t Array5.t = {
    var aux: W128.t;
    var aux_0: W128.t Array5.t;
    
    var xy0:W128.t option Array5.t;
    var t:W128.t option Array5.t;
    var z:W128.t option Array5.t;
    t <- Array5.init None;
    xy0 <- Array5.init None;
    z <- Array5.init None;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[0]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[1]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[2]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[3]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init y.[4]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[4]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[0]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[1]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[2]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[3]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[0]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[0]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[1]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[2]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[3]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[4]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[1]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[2]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget y.[0]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget y.[1]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget y.[0]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[0]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[1]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[2]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[3]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[4]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 0 4/\ is_init yx5.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[0]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[1]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[1]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget yx5.[2]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[2]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[0]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[2]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[1]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[4]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[3]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[2]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget yx5.[3]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget yx5.[3]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[3]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[3]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    aux_0 <@ unpack_u128x2_to_u26x5x2 (in_0);
    xy0 <- aux_0;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[0]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[1]);
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[2]);
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[3]);
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[4]);
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init t.[4];
    aux <- (oget t.[4]);
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    return (x, (oget xy0));
  }
  
  proc mulmod_add_u128_prefetch (in_0:W64.t, u:W128.t Array5.t,
                                 x:W128.t Array5.t, y:W128.t Array5.t,
                                 yx5:W128.t Array4.t) : W128.t Array5.t *
                                                        W128.t Array5.t = {
    var aux: W128.t;
    var aux_0: W128.t Array5.t;
    
    var xy1:W128.t option Array5.t;
    var t:W128.t option Array5.t;
    var z:W128.t option Array5.t;
    t <- Array5.init None;
    xy1 <- Array5.init None;
    z <- Array5.init None;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[0]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[1]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[2]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[3]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init y.[4]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPMULU_128 (oget x.[0]) (oget y.[4]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    aux_0 <@ add_u128 ((oget t), u);
    t <- aux_0;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[0]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[1]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[2]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init y.[3]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget y.[3]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[0]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[0]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[1]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[2]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[3]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[4]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[1]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init y.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget y.[2]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget y.[0]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init y.[1]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget y.[1]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init y.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget y.[0]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[0]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[1]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[2]);
    safe <- safe /\ in_bound 3 5;
    t.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[3]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 4 5/\
            is_init t.[4];
    aux <- x86_VPADD_2u64 (oget t.[4]) (oget z.[4]);
    safe <- safe /\ in_bound 4 5;
    t.[4] <- Some aux;
    safe <- safe /\ in_bound 0 4/\ is_init yx5.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[0]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[1]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 4/\ is_init yx5.[1]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[1]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget yx5.[2]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[2]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[0]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[2]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[1]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[4]);
    safe <- safe /\ in_bound 1 5;
    t.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[3]);
    safe <- safe /\ in_bound 0 5;
    t.[0] <- Some aux;
    safe <- safe /\ in_bound 2 4/\ is_init yx5.[2]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[2]);
    safe <- safe /\ in_bound 0 5;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPMULU_128 (oget x.[1]) (oget yx5.[3]);
    safe <- safe /\ in_bound 1 5;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPMULU_128 (oget x.[2]) (oget yx5.[3]);
    safe <- safe /\ in_bound 2 5;
    z.[2] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPMULU_128 (oget x.[3]) (oget yx5.[3]);
    safe <- safe /\ in_bound 3 5;
    z.[3] <- Some aux;
    safe <- safe /\ in_bound 3 4/\ is_init yx5.[3]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPMULU_128 (oget x.[4]) (oget yx5.[3]);
    safe <- safe /\ in_bound 4 5;
    z.[4] <- Some aux;
    aux_0 <@ unpack_u128x2_to_u26x5x2 (in_0);
    xy1 <- aux_0;
    safe <- safe /\ in_bound 0 5/\ is_init z.[0]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[0]);
    safe <- safe /\ in_bound 2 5;
    t.[2] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init z.[1]/\ in_bound 0 5/\
            is_init t.[0];
    aux <- x86_VPADD_2u64 (oget t.[0]) (oget z.[1]);
    safe <- safe /\ in_bound 0 5;
    u.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init z.[2]/\ in_bound 1 5/\
            is_init t.[1];
    aux <- x86_VPADD_2u64 (oget t.[1]) (oget z.[2]);
    safe <- safe /\ in_bound 1 5;
    u.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init z.[3]/\ in_bound 2 5/\
            is_init t.[2];
    aux <- x86_VPADD_2u64 (oget t.[2]) (oget z.[3]);
    safe <- safe /\ in_bound 2 5;
    u.[2] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init z.[4]/\ in_bound 3 5/\
            is_init t.[3];
    aux <- x86_VPADD_2u64 (oget t.[3]) (oget z.[4]);
    safe <- safe /\ in_bound 3 5;
    u.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init t.[4];
    aux <- (oget t.[4]);
    safe <- safe /\ in_bound 4 5;
    u.[4] <- Some aux;
    return (u, (oget xy1));
  }
  
  proc carry_reduce_u128 (x:W128.t Array5.t) : W128.t Array5.t = {
    var aux: W128.t;
    
    var z:W128.t option Array2.t;
    z <- Array2.init None;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- x86_VPSRL_2u64 (oget x.[0]) (W8.of_uint 26);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- x86_VPSRL_2u64 (oget x.[3]) (W8.of_uint 26);
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- x86_VPAND_128 (oget x.[0]) mask26_u128;
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- x86_VPAND_128 (oget x.[3]) mask26_u128;
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPADD_2u64 (oget x.[1]) (oget z.[0]);
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPADD_2u64 (oget x.[4]) (oget z.[1]);
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- x86_VPSRL_2u64 (oget x.[1]) (W8.of_uint 26);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- x86_VPSRL_2u64 (oget x.[4]) (W8.of_uint 26);
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1];
    aux <- x86_VPMULU_128 (oget z.[1]) five_u128;
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- x86_VPAND_128 (oget x.[1]) mask26_u128;
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- x86_VPAND_128 (oget x.[4]) mask26_u128;
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 2 5/\
            is_init x.[2];
    aux <- x86_VPADD_2u64 (oget x.[2]) (oget z.[0]);
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1]/\ in_bound 0 5/\
            is_init x.[0];
    aux <- x86_VPADD_2u64 (oget x.[0]) (oget z.[1]);
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- x86_VPSRL_2u64 (oget x.[2]) (W8.of_uint 26);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- x86_VPSRL_2u64 (oget x.[0]) (W8.of_uint 26);
    safe <- safe /\ in_bound 1 2;
    z.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- x86_VPAND_128 (oget x.[2]) mask26_u128;
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- x86_VPAND_128 (oget x.[0]) mask26_u128;
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 3 5/\
            is_init x.[3];
    aux <- x86_VPADD_2u64 (oget x.[3]) (oget z.[0]);
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init z.[1]/\ in_bound 1 5/\
            is_init x.[1];
    aux <- x86_VPADD_2u64 (oget x.[1]) (oget z.[1]);
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- x86_VPSRL_2u64 (oget x.[3]) (W8.of_uint 26);
    safe <- safe /\ in_bound 0 2;
    z.[0] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- x86_VPAND_128 (oget x.[3]) mask26_u128;
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init z.[0]/\ in_bound 4 5/\
            is_init x.[4];
    aux <- x86_VPADD_2u64 (oget x.[4]) (oget z.[0]);
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    return (x);
  }
  
  proc clamp (k:W64.t) : W64.t Array5.t = {
    var aux_0: W64.t;
    var aux: W64.t Array5.t;
    
    var r:W64.t option Array5.t;
    r <- Array5.init None;
    aux <@ unpack (k);
    r <- aux;
    safe <- safe /\ in_bound 0 5/\ is_init r.[0];
    aux_0 <- ((oget r.[0]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 0 5;
    r.[0] <- Some aux_0;
    safe <- safe /\ in_bound 1 5/\ is_init r.[1];
    aux_0 <- ((oget r.[1]) `&` (W64.of_uint 67108611));
    safe <- safe /\ in_bound 1 5;
    r.[1] <- Some aux_0;
    safe <- safe /\ in_bound 2 5/\ is_init r.[2];
    aux_0 <- ((oget r.[2]) `&` (W64.of_uint 67092735));
    safe <- safe /\ in_bound 2 5;
    r.[2] <- Some aux_0;
    safe <- safe /\ in_bound 3 5/\ is_init r.[3];
    aux_0 <- ((oget r.[3]) `&` (W64.of_uint 66076671));
    safe <- safe /\ in_bound 3 5;
    r.[3] <- Some aux_0;
    safe <- safe /\ in_bound 4 5/\ is_init r.[4];
    aux_0 <- ((oget r.[4]) `&` (W64.of_uint 1048575));
    safe <- safe /\ in_bound 4 5;
    r.[4] <- Some aux_0;
    return ((oget r));
  }
  
  proc load (in_0:W64.t) : W64.t Array5.t = {
    var aux_0: W64.t;
    var aux: W64.t Array5.t;
    
    var x:W64.t option Array5.t;
    x <- Array5.init None;
    aux <@ unpack (in_0);
    x <- aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux_0 <- ((oget x.[4]) `|` (W64.of_uint 16777216));
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux_0;
    return ((oget x));
  }
  
  proc load_last (in_0:W64.t, inlen:W64.t) : W64.t Array5.t = {
    var aux: W64.t;
    
    var x:W64.t option Array5.t;
    var i:int option;
    var m:W64.t option Array2.t;
    var c:W64.t option;
    var n:W64.t option;
    var t:W64.t option;
    m <- Array2.init None;
    x <- Array5.init None;
    i <- Some 0;
    while ((oget i) < 2) {
      aux <- (W64.of_uint 0);
      safe <- safe /\ in_bound (oget i) 2/\ is_init i;
      m.[(oget i)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    if ((inlen \ult (W64.of_uint 8))) {
      aux <- (W64.of_uint 0);
      c <- Some aux;
      aux <- (W64.of_uint 0);
      n <- Some aux;
      
      safe <- safe /\ is_init c;
      
      while (((oget c) \ult inlen)) {
        safe <- safe /\ is_valid Glob.mem (in_0 + (oget c)) W8/\ is_init c;
        aux <- (zeroext_8_64 (loadW8 Glob.mem (in_0 + (oget c))));
        t <- Some aux;
        safe <- safe /\ is_init n/\ is_init t;
        aux <- ((oget t) `<<` (zeroext_64_8 (oget n)));
        t <- Some aux;
        safe <- safe /\ is_init t/\ in_bound 0 2/\ is_init m.[0];
        aux <- ((oget m.[0]) `|` (oget t));
        safe <- safe /\ in_bound 0 2;
        m.[0] <- Some aux;
        safe <- safe /\ is_init n;
        aux <- ((oget n) + (W64.of_uint 8));
        n <- Some aux;
        safe <- safe /\ is_init c;
        aux <- ((oget c) + (W64.of_uint 1));
        c <- Some aux;
      safe <- safe /\ is_init c;
      
      }
      aux <- (W64.of_uint 1);
      t <- Some aux;
      safe <- safe /\ is_init n/\ is_init t;
      aux <- ((oget t) `<<` (zeroext_64_8 (oget n)));
      t <- Some aux;
      safe <- safe /\ is_init t/\ in_bound 0 2/\ is_init m.[0];
      aux <- ((oget m.[0]) `|` (oget t));
      safe <- safe /\ in_bound 0 2;
      m.[0] <- Some aux;
    } else {
      safe <- safe /\ is_valid Glob.mem (in_0 + (W64.of_uint 0)) W64;
      aux <- (loadW64 Glob.mem (in_0 + (W64.of_uint 0)));
      safe <- safe /\ in_bound 0 2;
      m.[0] <- Some aux;
      aux <- (inlen - (W64.of_uint 8));
      inlen <- aux;
      aux <- (in_0 + (W64.of_uint 8));
      in_0 <- aux;
      aux <- (W64.of_uint 0);
      c <- Some aux;
      aux <- (W64.of_uint 0);
      n <- Some aux;
      
      safe <- safe /\ is_init c;
      
      while (((oget c) \ult inlen)) {
        safe <- safe /\ is_valid Glob.mem (in_0 + (oget c)) W8/\ is_init c;
        aux <- (zeroext_8_64 (loadW8 Glob.mem (in_0 + (oget c))));
        t <- Some aux;
        safe <- safe /\ is_init n/\ is_init t;
        aux <- ((oget t) `<<` (zeroext_64_8 (oget n)));
        t <- Some aux;
        safe <- safe /\ is_init t/\ in_bound 1 2/\ is_init m.[1];
        aux <- ((oget m.[1]) `|` (oget t));
        safe <- safe /\ in_bound 1 2;
        m.[1] <- Some aux;
        safe <- safe /\ is_init n;
        aux <- ((oget n) + (W64.of_uint 8));
        n <- Some aux;
        safe <- safe /\ is_init c;
        aux <- ((oget c) + (W64.of_uint 1));
        c <- Some aux;
      safe <- safe /\ is_init c;
      
      }
      aux <- (W64.of_uint 1);
      t <- Some aux;
      safe <- safe /\ is_init n/\ is_init t;
      aux <- ((oget t) `<<` (zeroext_64_8 (oget n)));
      t <- Some aux;
      safe <- safe /\ is_init t/\ in_bound 1 2/\ is_init m.[1];
      aux <- ((oget m.[1]) `|` (oget t));
      safe <- safe /\ in_bound 1 2;
      m.[1] <- Some aux;
    }
    safe <- safe /\ in_bound 0 2/\ is_init m.[0];
    aux <- (oget m.[0]);
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- ((oget x.[0]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 0 5;
    x.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init m.[0];
    aux <- ((oget m.[0]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 0 2;
    m.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init m.[0];
    aux <- (oget m.[0]);
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- ((oget x.[1]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 1 5;
    x.[1] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init m.[0];
    aux <- ((oget m.[0]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 0 2;
    m.[0] <- Some aux;
    safe <- safe /\ in_bound 0 2/\ is_init m.[0];
    aux <- (oget m.[0]);
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init m.[1];
    aux <- (oget m.[1]);
    t <- Some aux;
    safe <- safe /\ is_init t;
    aux <- ((oget t) `<<` (W8.of_uint 12));
    t <- Some aux;
    safe <- safe /\ is_init t/\ in_bound 2 5/\ is_init x.[2];
    aux <- ((oget x.[2]) `|` (oget t));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- ((oget x.[2]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 2 5;
    x.[2] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init m.[1];
    aux <- ((oget m.[1]) `>>` (W8.of_uint 14));
    safe <- safe /\ in_bound 1 2;
    m.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init m.[1];
    aux <- (oget m.[1]);
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- ((oget x.[3]) `&` (W64.of_uint 67108863));
    safe <- safe /\ in_bound 3 5;
    x.[3] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init m.[1];
    aux <- ((oget m.[1]) `>>` (W8.of_uint 26));
    safe <- safe /\ in_bound 1 2;
    m.[1] <- Some aux;
    safe <- safe /\ in_bound 1 2/\ is_init m.[1];
    aux <- (oget m.[1]);
    safe <- safe /\ in_bound 4 5;
    x.[4] <- Some aux;
    return ((oget x));
  }
  
  proc pack (y:W64.t, x:W64.t Array5.t) : unit = {
    var aux: W64.t;
    
    var t:W64.t option;
    var t1:W64.t option;
    
    safe <- safe /\ in_bound 0 5/\ is_init x.[0];
    aux <- (oget x.[0]);
    t <- Some aux;
    safe <- safe /\ in_bound 1 5/\ is_init x.[1];
    aux <- (oget x.[1]);
    t1 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- ((oget t1) `<<` (W8.of_uint 26));
    t1 <- Some aux;
    safe <- safe /\ is_init t1/\ is_init t;
    aux <- ((oget t) `|` (oget t1));
    t <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    t1 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- ((oget t1) `<<` (W8.of_uint 52));
    t1 <- Some aux;
    safe <- safe /\ is_init t1/\ is_init t;
    aux <- ((oget t) `|` (oget t1));
    t <- Some aux;
    safe <- safe /\ is_init t;
    aux <- (oget t);
    safe <- safe /\ is_valid Glob.mem (y + (W64.of_uint (0 * 8))) W64;
    Glob.mem <- storeW64 Glob.mem (y + (W64.of_uint (0 * 8))) aux;
    safe <- safe /\ in_bound 2 5/\ is_init x.[2];
    aux <- (oget x.[2]);
    t <- Some aux;
    safe <- safe /\ is_init t;
    aux <- ((oget t) `&` (W64.of_uint 67108863));
    t <- Some aux;
    safe <- safe /\ is_init t;
    aux <- ((oget t) `>>` (W8.of_uint 12));
    t <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init x.[3];
    aux <- (oget x.[3]);
    t1 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- ((oget t1) `<<` (W8.of_uint 14));
    t1 <- Some aux;
    safe <- safe /\ is_init t1/\ is_init t;
    aux <- ((oget t) `|` (oget t1));
    t <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init x.[4];
    aux <- (oget x.[4]);
    t1 <- Some aux;
    safe <- safe /\ is_init t1;
    aux <- ((oget t1) `<<` (W8.of_uint 40));
    t1 <- Some aux;
    safe <- safe /\ is_init t1/\ is_init t;
    aux <- ((oget t) `|` (oget t1));
    t <- Some aux;
    safe <- safe /\ is_init t;
    aux <- (oget t);
    safe <- safe /\ is_valid Glob.mem (y + (W64.of_uint (1 * 8))) W64;
    Glob.mem <- storeW64 Glob.mem (y + (W64.of_uint (1 * 8))) aux;
    return ();
  }
  
  proc first_block (in_0:W64.t, s_r2r2:W128.t Array5.t,
                    s_r2r2x5:W128.t Array4.t) : W128.t Array5.t * W64.t = {
    var aux_0: W64.t;
    var aux: W128.t Array5.t;
    
    var hxy:W128.t option Array5.t;
    var xy0:W128.t option Array5.t;
    var xy1:W128.t option Array5.t;
    hxy <- Array5.init None;
    xy0 <- Array5.init None;
    xy1 <- Array5.init None;
    aux <@ unpack_u128x2_to_u26x5x2 (in_0);
    xy0 <- aux;
    aux_0 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_0;
    aux <@ mulmod_u128 ((oget xy0), s_r2r2, s_r2r2x5);
    hxy <- aux;
    aux <@ unpack_u128x2_to_u26x5x2 (in_0);
    xy1 <- aux;
    aux_0 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_0;
    aux <@ add_u128 ((oget hxy), (oget xy1));
    hxy <- aux;
    aux <@ carry_reduce_u128 ((oget hxy));
    hxy <- aux;
    return ((oget hxy), in_0);
  }
  
  proc remaining_blocks (hxy:W128.t Array5.t, in_0:W64.t,
                         s_r4r4:W128.t Array5.t, s_r4r4x5:W128.t Array4.t,
                         s_r2r2:W128.t Array5.t, s_r2r2x5:W128.t Array4.t) : 
  W128.t Array5.t * W64.t = {
    var aux_1: W64.t;
    var aux_0: W128.t Array5.t;
    var aux: W128.t Array5.t;
    
    var xy0:W128.t option Array5.t;
    var xy1:W128.t option Array5.t;
    xy0 <- Array5.init None;
    xy1 <- Array5.init None;
    (aux_0, aux) <@ mulmod_u128_prefetch (in_0, hxy, s_r4r4, s_r4r4x5);
    hxy <- aux_0;
    xy0 <- aux;
    aux_1 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_1;
    (aux_0, aux) <@ mulmod_add_u128_prefetch (in_0, hxy, (oget xy0), s_r2r2,
    s_r2r2x5);
    hxy <- aux_0;
    xy1 <- aux;
    aux_1 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_1;
    aux_0 <@ add_u128 (hxy, (oget xy1));
    hxy <- aux_0;
    aux_0 <@ carry_reduce_u128 (hxy);
    hxy <- aux_0;
    return (hxy, in_0);
  }
  
  proc final_mul (hxy:W128.t Array5.t, s_r2r:W128.t Array5.t,
                  s_r2rx5:W128.t Array4.t) : W64.t Array5.t = {
    var aux_0: W64.t Array5.t;
    var aux: W128.t Array5.t;
    
    var h:W64.t option Array5.t;
    h <- Array5.init None;
    aux <@ mulmod_u128 (hxy, s_r2r, s_r2rx5);
    hxy <- aux;
    aux <@ carry_reduce_u128 (hxy);
    hxy <- aux;
    aux_0 <@ hadd_u128 (hxy);
    h <- aux_0;
    return ((oget h));
  }
  
  proc poly1305 (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    var aux: W64.t;
    var aux_2: W128.t;
    var aux_0: W64.t Array5.t;
    var aux_1: W128.t Array5.t;
    
    var s_out:W64.t option;
    var s_in:W64.t option;
    var s_inlen:W64.t option;
    var s_k:W64.t option;
    var r:W64.t option Array5.t;
    var s_r:W64.t option Array5.t;
    var i:int option;
    var t:W64.t option;
    var s_rx5:W64.t option Array4.t;
    var h:W64.t option Array5.t;
    var b64:W64.t option;
    var s_b64:W64.t option;
    var r2:W64.t option Array5.t;
    var s_r2:W64.t option Array5.t;
    var s_r2x5:W64.t option Array4.t;
    var r2r:W128.t option Array5.t;
    var s_r2r:W128.t option Array5.t;
    var t_u128:W128.t option;
    var s_r2rx5:W128.t option Array4.t;
    var r2r2:W128.t option Array5.t;
    var s_r2r2:W128.t option Array5.t;
    var s_r2r2x5:W128.t option Array4.t;
    var r4:W64.t option Array5.t;
    var r4r4:W128.t option Array5.t;
    var s_r4r4:W128.t option Array5.t;
    var s_r4r4x5:W128.t option Array4.t;
    var hxy:W128.t option Array5.t;
    var b16:W64.t option;
    var x:W64.t option Array5.t;
    var s:W64.t option Array5.t;
    h <- Array5.init None;
    hxy <- Array5.init None;
    r <- Array5.init None;
    r2 <- Array5.init None;
    r2r <- Array5.init None;
    r2r2 <- Array5.init None;
    r4 <- Array5.init None;
    r4r4 <- Array5.init None;
    s <- Array5.init None;
    s_r <- Array5.init None;
    s_r2 <- Array5.init None;
    s_r2r <- Array5.init None;
    s_r2r2 <- Array5.init None;
    s_r2r2x5 <- Array4.init None;
    s_r2rx5 <- Array4.init None;
    s_r2x5 <- Array4.init None;
    s_r4r4 <- Array5.init None;
    s_r4r4x5 <- Array4.init None;
    s_rx5 <- Array4.init None;
    x <- Array5.init None;
    aux <- out;
    s_out <- Some aux;
    aux <- in_0;
    s_in <- Some aux;
    aux <- inlen;
    s_inlen <- Some aux;
    aux <- k;
    s_k <- Some aux;
    aux_0 <@ clamp (k);
    r <- aux_0;
    aux_0 <- (oget r);
    s_r <- aux_0;
    i <- Some 0;
    while ((oget i) < 4) {
      safe <- safe /\ in_bound ((oget i) + 1) 5/\
              is_init r.[((oget i) + 1)]/\ is_init i;
      aux <- ((oget r.[((oget i) + 1)]) * (W64.of_uint 5));
      t <- Some aux;
      safe <- safe /\ is_init t;
      aux <- (oget t);
      safe <- safe /\ in_bound (oget i) 4/\ is_init i;
      s_rx5.[(oget i)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    i <- Some 0;
    while ((oget i) < 5) {
      aux <- (W64.of_uint 0);
      safe <- safe /\ in_bound (oget i) 5/\ is_init i;
      h.[(oget i)] <- Some aux;
      i <- Some ((oget i) + 1);
    }
    aux <- inlen;
    b64 <- Some aux;
    safe <- safe /\ is_init b64;
    aux <- ((oget b64) `>>` (W8.of_uint 6));
    b64 <- Some aux;
    safe <- safe /\ is_init b64;
    if (((W64.of_uint 0) \ult (oget b64))) {
      safe <- safe /\ is_init b64;
      aux <- (oget b64);
      s_b64 <- Some aux;
      aux_0 <- (oget r);
      r2 <- aux_0;
      aux_0 <@ mulmod_12 ((oget r2), (oget s_r), (oget s_rx5));
      r2 <- aux_0;
      aux_0 <@ carry_reduce ((oget r2));
      r2 <- aux_0;
      aux_0 <- (oget r2);
      s_r2 <- aux_0;
      i <- Some 0;
      while ((oget i) < 4) {
        safe <- safe /\ in_bound ((oget i) + 1) 5/\
                is_init r2.[((oget i) + 1)]/\ is_init i;
        aux <- ((oget r2.[((oget i) + 1)]) * (W64.of_uint 5));
        t <- Some aux;
        safe <- safe /\ is_init t;
        aux <- (oget t);
        safe <- safe /\ in_bound (oget i) 4/\ is_init i;
        s_r2x5.[(oget i)] <- Some aux;
        i <- Some ((oget i) + 1);
      }
      aux_0 <- (oget s_r);
      r <- aux_0;
      aux_1 <@ unpack_u26x5x2_to_u26x5x2 ((oget r2), (oget r));
      r2r <- aux_1;
      aux_1 <- (oget r2r);
      s_r2r <- aux_1;
      i <- Some 0;
      while ((oget i) < 4) {
        safe <- safe /\ in_bound ((oget i) + 1) 5/\
                is_init r2r.[((oget i) + 1)]/\ is_init i;
        aux_2 <- x86_VPMULU_128 (oget r2r.[((oget i) + 1)]) five_u128;
        t_u128 <- Some aux_2;
        safe <- safe /\ is_init t_u128;
        aux_2 <- (oget t_u128);
        safe <- safe /\ in_bound (oget i) 4/\ is_init i;
        s_r2rx5.[(oget i)] <- Some aux_2;
        i <- Some ((oget i) + 1);
      }
      aux_1 <@ unpack_u26x5x2_to_u26x5x2 ((oget r2), (oget r2));
      r2r2 <- aux_1;
      aux_1 <- (oget r2r2);
      s_r2r2 <- aux_1;
      i <- Some 0;
      while ((oget i) < 4) {
        safe <- safe /\ in_bound ((oget i) + 1) 5/\
                is_init r2r2.[((oget i) + 1)]/\ is_init i;
        aux_2 <- x86_VPMULU_128 (oget r2r2.[((oget i) + 1)]) five_u128;
        t_u128 <- Some aux_2;
        safe <- safe /\ is_init t_u128;
        aux_2 <- (oget t_u128);
        safe <- safe /\ in_bound (oget i) 4/\ is_init i;
        s_r2r2x5.[(oget i)] <- Some aux_2;
        i <- Some ((oget i) + 1);
      }
      safe <- safe /\ is_init s_b64;
      aux <- (oget s_b64);
      b64 <- Some aux;
      safe <- safe /\ is_init b64;
      if (((W64.of_uint 1) \ult (oget b64))) {
        aux_0 <- (oget r2);
        r4 <- aux_0;
        aux_0 <@ mulmod_12 ((oget r4), (oget s_r2), (oget s_r2x5));
        r4 <- aux_0;
        aux_0 <@ carry_reduce ((oget r4));
        r4 <- aux_0;
        aux_1 <@ unpack_u26x5x2_to_u26x5x2 ((oget r4), (oget r4));
        r4r4 <- aux_1;
        aux_1 <- (oget r4r4);
        s_r4r4 <- aux_1;
        i <- Some 0;
        while ((oget i) < 4) {
          safe <- safe /\ in_bound ((oget i) + 1) 5/\
                  is_init r4r4.[((oget i) + 1)]/\ is_init i;
          aux_2 <- x86_VPMULU_128 (oget r4r4.[((oget i) + 1)]) five_u128;
          t_u128 <- Some aux_2;
          safe <- safe /\ is_init t_u128;
          aux_2 <- (oget t_u128);
          safe <- safe /\ in_bound (oget i) 4/\ is_init i;
          s_r4r4x5.[(oget i)] <- Some aux_2;
          i <- Some ((oget i) + 1);
        }
      } else {
        
      }
      safe <- safe /\ is_init s_in;
      aux <- (oget s_in);
      in_0 <- aux;
      (aux_1, aux) <@ first_block (in_0, (oget s_r2r2), (oget s_r2r2x5));
      hxy <- aux_1;
      in_0 <- aux;
      safe <- safe /\ is_init s_b64;
      aux <- (oget s_b64);
      b64 <- Some aux;
      safe <- safe /\ is_init b64;
      aux <- ((oget b64) - (W64.of_uint 1));
      b64 <- Some aux;
      
      safe <- safe /\ is_init b64;
      
      while (((W64.of_uint 0) \ult (oget b64))) {
        safe <- safe /\ is_init b64;
        aux <- ((oget b64) - (W64.of_uint 1));
        b64 <- Some aux;
        safe <- safe /\ is_init b64;
        aux <- (oget b64);
        s_b64 <- Some aux;
        (aux_1, aux) <@ remaining_blocks ((oget hxy), in_0, (oget s_r4r4),
        (oget s_r4r4x5), (oget s_r2r2), (oget s_r2r2x5));
        hxy <- aux_1;
        in_0 <- aux;
        safe <- safe /\ is_init s_b64;
        aux <- (oget s_b64);
        b64 <- Some aux;
      safe <- safe /\ is_init b64;
      
      }
      aux_0 <@ final_mul ((oget hxy), (oget s_r2r), (oget s_r2rx5));
      h <- aux_0;
    } else {
      
    }
    safe <- safe /\ is_init s_inlen;
    aux <- (oget s_inlen);
    b16 <- Some aux;
    safe <- safe /\ is_init b16;
    aux <- ((oget b16) `>>` (W8.of_uint 4));
    b16 <- Some aux;
    safe <- safe /\ is_init b16;
    aux <- ((oget b16) `&` (W64.of_uint 3));
    b16 <- Some aux;
    
    safe <- safe /\ is_init b16;
    
    while (((W64.of_uint 0) \ult (oget b16))) {
      safe <- safe /\ is_init b16;
      aux <- ((oget b16) - (W64.of_uint 1));
      b16 <- Some aux;
      aux_0 <@ load (in_0);
      x <- aux_0;
      aux <- (in_0 + (W64.of_uint 16));
      in_0 <- aux;
      aux_0 <@ add ((oget h), (oget x));
      h <- aux_0;
      aux_0 <@ mulmod_12 ((oget h), (oget s_r), (oget s_rx5));
      h <- aux_0;
      aux_0 <@ carry_reduce ((oget h));
      h <- aux_0;
    safe <- safe /\ is_init b16;
    
    }
    safe <- safe /\ is_init s_inlen;
    aux <- (oget s_inlen);
    inlen <- aux;
    aux <- (inlen `&` (W64.of_uint 15));
    inlen <- aux;
    if ((inlen <> (W64.of_uint 0))) {
      aux_0 <@ load_last (in_0, inlen);
      x <- aux_0;
      aux_0 <@ add ((oget h), (oget x));
      h <- aux_0;
      aux_0 <@ mulmod_12 ((oget h), (oget s_r), (oget s_rx5));
      h <- aux_0;
      aux_0 <@ carry_reduce ((oget h));
      h <- aux_0;
    } else {
      
    }
    aux_0 <@ freeze ((oget h));
    h <- aux_0;
    safe <- safe /\ is_init s_k;
    aux <- (oget s_k);
    k <- aux;
    aux <- (k + (W64.of_uint 16));
    k <- aux;
    safe <- safe /\ is_init s_out;
    aux <- (oget s_out);
    out <- aux;
    aux_0 <@ unpack (k);
    s <- aux_0;
    aux_0 <@ add_carry ((oget h), (oget s));
    h <- aux_0;
    pack (out, (oget h));
    return ();
  }
}.

