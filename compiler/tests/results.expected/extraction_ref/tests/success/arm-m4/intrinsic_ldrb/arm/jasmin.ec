require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc ldrb (arg:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (arg + (W32.of_int 0))));
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 2))));
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 2)))));
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (x + arg)));
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 1)))));
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2)))));
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 4)))));
    x <- LDRB (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 8)))));
    (n, z, c, v) <- CMP x (W32.of_int 0);
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) z x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! z) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) c x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! c) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) n x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! n) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) v x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! v) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (c /\ (! z)) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) ((! c) \/ z) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (n = v) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (! (n = v)) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) ((! z) /\ (n = v)) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 0)))) (z \/ (! (n = v))) x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + arg))) z x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (W32.of_int 3)))) z x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (- (W32.of_int 3))))) z x;
    x <- LDRBcc (loadW8 Glob.mem (W32.to_uint (x + (arg * (W32.of_int 2))))) z x;
    res_0 <- x;
    return (res_0);
  }
}.

