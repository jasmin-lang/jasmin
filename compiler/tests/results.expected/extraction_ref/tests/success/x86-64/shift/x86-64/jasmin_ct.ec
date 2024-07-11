require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.

abbrev g = Array1.of_list witness [W64.of_int 6009882477281497451].


module M = {
  var leakages : leakages_t
  
  proc test_shld (p:W64.t) : unit = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux_5: W8.t;
    var aux: W16.t;
    var aux_6: W32.t;
    var aux_7: W64.t;
    
    var a:W16.t;
    var b:W16.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var n:W8.t;
    var c:W32.t;
    var d:W32.t;
    var e:W64.t;
    var f:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 2)))]) :: leakages;
    aux <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 2))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- SHLD_16 a b (W8.of_int 3);
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _0 <- aux_1;
    _zf_ <- aux_0;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    n <- (truncateu8 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (n `&` (W8.of_int 15));
    n <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- SHLD_16 a b n;
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _1 <- aux_1;
    _zf_ <- aux_0;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_6 <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    c <- aux_6;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 4)))]) :: leakages;
    aux_6 <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))));
    d <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_6) <- SHLD_32 c d (W8.of_int 17);
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _2 <- aux_1;
    _zf_ <- aux_0;
    c <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W8.of_int 9);
    n <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_6) <- SHLD_32 c d n;
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _3 <- aux_1;
    _zf_ <- aux_0;
    c <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_6);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_7 <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    e <- aux_7;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 8)))]) :: leakages;
    aux_7 <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))));
    f <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_7) <- SHLD_64 f e (W8.of_int 17);
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _4 <- aux_1;
    _zf_ <- aux_0;
    f <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W8.of_int 11);
    n <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_7) <- SHLD_64 f e n;
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _5 <- aux_1;
    _zf_ <- aux_0;
    f <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_7 <- f;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_7);
    return ();
  }
  
  proc test_shrd (p:W64.t) : unit = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux_5: W8.t;
    var aux: W16.t;
    var aux_6: W32.t;
    var aux_7: W64.t;
    
    var a:W16.t;
    var b:W16.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var n:W8.t;
    var c:W32.t;
    var d:W32.t;
    var e:W64.t;
    var f:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 2)))]) :: leakages;
    aux <- (loadW16 Glob.mem (W64.to_uint (p + (W64.of_int 2))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- SHRD_16 a b (W8.of_int 3);
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _0 <- aux_1;
    _zf_ <- aux_0;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    n <- (truncateu8 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (n `&` (W8.of_int 15));
    n <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux) <- SHRD_16 a b n;
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _1 <- aux_1;
    _zf_ <- aux_0;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_6 <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    c <- aux_6;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 4)))]) :: leakages;
    aux_6 <- (loadW32 Glob.mem (W64.to_uint (p + (W64.of_int 4))));
    d <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_6) <- SHRD_32 c d (W8.of_int 17);
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _2 <- aux_1;
    _zf_ <- aux_0;
    c <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W8.of_int 9);
    n <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_6) <- SHRD_32 c d n;
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _3 <- aux_1;
    _zf_ <- aux_0;
    c <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- c;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_6);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_7 <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    e <- aux_7;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 8)))]) :: leakages;
    aux_7 <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))));
    f <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_7) <- SHRD_64 f e (W8.of_int 17);
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _4 <- aux_1;
    _zf_ <- aux_0;
    f <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W8.of_int 11);
    n <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_7) <- SHRD_64 f e n;
    _of_ <- aux_4;
    _cf_ <- aux_3;
    _sf_ <- aux_2;
     _5 <- aux_1;
    _zf_ <- aux_0;
    f <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_7 <- f;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_7);
    return ();
  }
  
  proc test_rorx (x:W64.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W64.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- RORX_64 x (W8.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- RORX_64 x (W8.of_int 1);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- RORX_64 x (W8.of_int (- 193));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- RORX_32 (truncateu32 x) (W8.of_int 1);
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- RORX_32 y (W8.of_int 17);
    y <- aux_0;
    return (y);
  }
  
  proc test_bmi_shifts (x:W64.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W64.t;
    
    var z:W32.t;
    var y:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- SARX_64 g.[0] x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SHRX_64 y x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- SHLX_64 x x;
    x <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- SARX_32 (get32 (WArray8.init64 (fun i => (g).[i])) 0) (truncateu32 x);
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- SHRX_32 z (truncateu32 x);
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- SHLX_32 (truncateu32 x) z;
    z <- aux_0;
    return (z);
  }
}.

