require import List Jasmin_model Int IntDiv CoreMap.




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
  
  proc mulmod_add_12 (u:W64.t Array5.t, x:W64.t Array5.t, y:W64.t Array5.t,
                      yx5:W64.t Array4.t) : W64.t Array5.t = {
    var aux: W64.t;
    var aux_0: W64.t Array5.t;
    
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
    aux_0 <@ add ((oget t), u);
    t <- aux_0;
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
    u.[0] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 0 5/\
            is_init u.[0];
    aux <- ((oget u.[0]) + (oget z.[0]));
    safe <- safe /\ in_bound 0 5;
    u.[0] <- Some aux;
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
    u.[1] <- Some aux;
    safe <- safe /\ in_bound 1 3/\ is_init z.[1]/\ in_bound 1 5/\
            is_init u.[1];
    aux <- ((oget u.[1]) + (oget z.[1]));
    safe <- safe /\ in_bound 1 5;
    u.[1] <- Some aux;
    safe <- safe /\ in_bound 2 5/\ is_init t.[2];
    aux <- (oget t.[2]);
    safe <- safe /\ in_bound 2 5;
    u.[2] <- Some aux;
    safe <- safe /\ in_bound 2 3/\ is_init z.[2]/\ in_bound 2 5/\
            is_init u.[2];
    aux <- ((oget u.[2]) + (oget z.[2]));
    safe <- safe /\ in_bound 2 5;
    u.[2] <- Some aux;
    safe <- safe /\ in_bound 3 5/\ is_init t.[3];
    aux <- (oget t.[3]);
    safe <- safe /\ in_bound 3 5;
    u.[3] <- Some aux;
    safe <- safe /\ in_bound 0 3/\ is_init z.[0]/\ in_bound 3 5/\
            is_init u.[3];
    aux <- ((oget u.[3]) + (oget z.[0]));
    safe <- safe /\ in_bound 3 5;
    u.[3] <- Some aux;
    safe <- safe /\ in_bound 4 5/\ is_init t.[4];
    aux <- (oget t.[4]);
    safe <- safe /\ in_bound 4 5;
    u.[4] <- Some aux;
    return (u);
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
  
  proc first_block (in_0:W64.t, s_r2:W64.t Array5.t, s_r2x5:W64.t Array4.t) : 
  W64.t Array5.t * W64.t Array5.t * W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array5.t;
    
    var hx:W64.t option Array5.t;
    var hy:W64.t option Array5.t;
    var x0:W64.t option Array5.t;
    var x1:W64.t option Array5.t;
    var s_hx:W64.t option Array5.t;
    var y0:W64.t option Array5.t;
    var y1:W64.t option Array5.t;
    hx <- Array5.init None;
    hy <- Array5.init None;
    s_hx <- Array5.init None;
    x0 <- Array5.init None;
    x1 <- Array5.init None;
    y0 <- Array5.init None;
    y1 <- Array5.init None;
    aux <@ load (in_0);
    x0 <- aux;
    aux_0 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_0;
    aux <@ mulmod_12 ((oget x0), s_r2, s_r2x5);
    hx <- aux;
    aux <@ load (in_0);
    x1 <- aux;
    aux_0 <- (in_0 - (W64.of_uint 16));
    in_0 <- aux_0;
    aux <@ add ((oget hx), (oget x1));
    hx <- aux;
    aux <@ carry_reduce ((oget hx));
    hx <- aux;
    aux <- (oget hx);
    s_hx <- aux;
    aux <@ load (in_0);
    y0 <- aux;
    aux_0 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_0;
    aux <@ mulmod_12 ((oget y0), s_r2, s_r2x5);
    hy <- aux;
    aux <@ load (in_0);
    y1 <- aux;
    aux <@ add ((oget hy), (oget y1));
    hy <- aux;
    aux <@ carry_reduce ((oget hy));
    hy <- aux;
    aux_0 <- (in_0 + (W64.of_uint 16));
    in_0 <- aux_0;
    aux <- (oget s_hx);
    hx <- aux;
    return ((oget hx), (oget hy), in_0);
  }
  
  proc remaining_blocks (hx:W64.t Array5.t, hy:W64.t Array5.t, in_0:W64.t,
                         s_r4:W64.t Array5.t, s_r4x5:W64.t Array4.t,
                         s_r2:W64.t Array5.t, s_r2x5:W64.t Array4.t) : 
  W64.t Array5.t * W64.t Array5.t * W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array5.t;
    
    var s_hy:W64.t option Array5.t;
    var x0:W64.t option Array5.t;
    var x1:W64.t option Array5.t;
    var s_hx:W64.t option Array5.t;
    var y0:W64.t option Array5.t;
    var y1:W64.t option Array5.t;
    s_hx <- Array5.init None;
    s_hy <- Array5.init None;
    x0 <- Array5.init None;
    x1 <- Array5.init None;
    y0 <- Array5.init None;
    y1 <- Array5.init None;
    aux <- hy;
    s_hy <- aux;
    aux <@ mulmod_12 (hx, s_r4, s_r4x5);
    hx <- aux;
    aux <@ load (in_0);
    x0 <- aux;
    aux_0 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_0;
    aux <@ mulmod_add_12 (hx, (oget x0), s_r2, s_r2x5);
    hx <- aux;
    aux <@ load (in_0);
    x1 <- aux;
    aux_0 <- (in_0 - (W64.of_uint 16));
    in_0 <- aux_0;
    aux <@ add (hx, (oget x1));
    hx <- aux;
    aux <@ carry_reduce (hx);
    hx <- aux;
    aux <- hx;
    s_hx <- aux;
    aux <- (oget s_hy);
    hy <- aux;
    aux <@ mulmod_12 (hy, s_r4, s_r4x5);
    hy <- aux;
    aux <@ load (in_0);
    y0 <- aux;
    aux_0 <- (in_0 + (W64.of_uint 32));
    in_0 <- aux_0;
    aux <@ mulmod_add_12 (hy, (oget y0), s_r2, s_r2x5);
    hy <- aux;
    aux <@ load (in_0);
    y1 <- aux;
    aux_0 <- (in_0 + (W64.of_uint 16));
    in_0 <- aux_0;
    aux <@ add (hy, (oget y1));
    hy <- aux;
    aux <@ carry_reduce (hy);
    hy <- aux;
    aux <- (oget s_hx);
    hx <- aux;
    return (hx, hy, in_0);
  }
  
  proc final_mul (hx:W64.t Array5.t, hy:W64.t Array5.t, s_r2:W64.t Array5.t,
                  s_r2x5:W64.t Array4.t, s_r:W64.t Array5.t,
                  s_rx5:W64.t Array4.t) : W64.t Array5.t = {
    var aux: W64.t Array5.t;
    
    var h:W64.t option Array5.t;
    var s_hy:W64.t option Array5.t;
    var s_hx:W64.t option Array5.t;
    h <- Array5.init None;
    s_hx <- Array5.init None;
    s_hy <- Array5.init None;
    aux <- hy;
    s_hy <- aux;
    aux <@ mulmod_12 (hx, s_r2, s_r2x5);
    hx <- aux;
    aux <@ carry_reduce (hx);
    hx <- aux;
    aux <- hx;
    s_hx <- aux;
    aux <- (oget s_hy);
    hy <- aux;
    aux <@ mulmod_12 (hy, s_r, s_rx5);
    hy <- aux;
    aux <@ carry_reduce (hy);
    hy <- aux;
    aux <- (oget s_hx);
    hx <- aux;
    aux <@ add_carry (hx, hy);
    h <- aux;
    return ((oget h));
  }
  
  proc poly1305 (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    var aux: W64.t;
    var aux_1: W64.t Array5.t;
    var aux_0: W64.t Array5.t;
    
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
    var r4:W64.t option Array5.t;
    var s_r4:W64.t option Array5.t;
    var s_r4x5:W64.t option Array4.t;
    var hx:W64.t option Array5.t;
    var hy:W64.t option Array5.t;
    var b16:W64.t option;
    var x:W64.t option Array5.t;
    var s:W64.t option Array5.t;
    h <- Array5.init None;
    hx <- Array5.init None;
    hy <- Array5.init None;
    r <- Array5.init None;
    r2 <- Array5.init None;
    r4 <- Array5.init None;
    s <- Array5.init None;
    s_r <- Array5.init None;
    s_r2 <- Array5.init None;
    s_r2x5 <- Array4.init None;
    s_r4 <- Array5.init None;
    s_r4x5 <- Array4.init None;
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
    aux_1 <@ clamp (k);
    r <- aux_1;
    aux_1 <- (oget r);
    s_r <- aux_1;
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
      aux_1 <- (oget r);
      r2 <- aux_1;
      aux_1 <@ mulmod_12 ((oget r2), (oget s_r), (oget s_rx5));
      r2 <- aux_1;
      aux_1 <@ carry_reduce ((oget r2));
      r2 <- aux_1;
      aux_1 <- (oget r2);
      s_r2 <- aux_1;
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
      safe <- safe /\ is_init s_b64;
      aux <- (oget s_b64);
      b64 <- Some aux;
      safe <- safe /\ is_init b64;
      if (((W64.of_uint 1) \ult (oget b64))) {
        aux_1 <- (oget r2);
        r4 <- aux_1;
        aux_1 <@ mulmod_12 ((oget r4), (oget s_r2), (oget s_r2x5));
        r4 <- aux_1;
        aux_1 <@ carry_reduce ((oget r4));
        r4 <- aux_1;
        aux_1 <- (oget r4);
        s_r4 <- aux_1;
        i <- Some 0;
        while ((oget i) < 4) {
          safe <- safe /\ in_bound ((oget i) + 1) 5/\
                  is_init r4.[((oget i) + 1)]/\ is_init i;
          aux <- ((oget r4.[((oget i) + 1)]) * (W64.of_uint 5));
          t <- Some aux;
          safe <- safe /\ is_init t;
          aux <- (oget t);
          safe <- safe /\ in_bound (oget i) 4/\ is_init i;
          s_r4x5.[(oget i)] <- Some aux;
          i <- Some ((oget i) + 1);
        }
      } else {
        
      }
      safe <- safe /\ is_init s_in;
      aux <- (oget s_in);
      in_0 <- aux;
      (aux_1, aux_0, aux) <@ first_block (in_0, (oget s_r2), (oget s_r2x5));
      hx <- aux_1;
      hy <- aux_0;
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
        (aux_1, aux_0, aux) <@ remaining_blocks ((oget hx), (oget hy), in_0,
        (oget s_r4), (oget s_r4x5), (oget s_r2), (oget s_r2x5));
        hx <- aux_1;
        hy <- aux_0;
        in_0 <- aux;
        safe <- safe /\ is_init s_b64;
        aux <- (oget s_b64);
        b64 <- Some aux;
      safe <- safe /\ is_init b64;
      
      }
      aux_1 <@ final_mul ((oget hx), (oget hy), (oget s_r2), (oget s_r2x5),
      (oget s_r), (oget s_rx5));
      h <- aux_1;
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
      aux_1 <@ load (in_0);
      x <- aux_1;
      aux <- (in_0 + (W64.of_uint 16));
      in_0 <- aux;
      aux_1 <@ add ((oget h), (oget x));
      h <- aux_1;
      aux_1 <@ mulmod_12 ((oget h), (oget s_r), (oget s_rx5));
      h <- aux_1;
      aux_1 <@ carry_reduce ((oget h));
      h <- aux_1;
    safe <- safe /\ is_init b16;
    
    }
    safe <- safe /\ is_init s_inlen;
    aux <- (oget s_inlen);
    inlen <- aux;
    aux <- (inlen `&` (W64.of_uint 15));
    inlen <- aux;
    if ((inlen <> (W64.of_uint 0))) {
      aux_1 <@ load_last (in_0, inlen);
      x <- aux_1;
      aux_1 <@ add ((oget h), (oget x));
      h <- aux_1;
      aux_1 <@ mulmod_12 ((oget h), (oget s_r), (oget s_rx5));
      h <- aux_1;
      aux_1 <@ carry_reduce ((oget h));
      h <- aux_1;
    } else {
      
    }
    aux_1 <@ freeze ((oget h));
    h <- aux_1;
    safe <- safe /\ is_init s_k;
    aux <- (oget s_k);
    k <- aux;
    aux <- (k + (W64.of_uint 16));
    k <- aux;
    safe <- safe /\ is_init s_out;
    aux <- (oget s_out);
    out <- aux;
    aux_1 <@ unpack (k);
    s <- aux_1;
    aux_1 <@ add_carry ((oget h), (oget s));
    h <- aux_1;
    pack (out, (oget h));
    return ();
  }
}.

