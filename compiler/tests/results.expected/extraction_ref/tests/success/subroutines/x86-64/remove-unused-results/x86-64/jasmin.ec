require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc aux (a:W256.t, b:W256.t, c:W256.t) : W256.t * W256.t * W256.t = {
    
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    x <- (a `^` b);
    y <- (a `^` c);
    z <- (b `^` c);
    return (x, y, z);
  }
  
  proc f (x:W256.t, y:W256.t) : W256.t = {
    
    var r:W256.t;
    var m:W256.t;
    var n:W256.t;
    var p:W256.t;
    
    m <- x;
    (m, n, p) <@ aux (x, m, y);
    r <- (m `^` p);
    return (r);
  }
  
  proc main (q:W64.t) : unit = {
    
    var u:W256.t;
    var v:W256.t;
    var w:W256.t;
    
    u <- (loadW256 Glob.mem (W64.to_uint (q + (W64.of_int 0))));
    v <- (loadW256 Glob.mem (W64.to_uint (q + (W64.of_int 32))));
    w <@ f (u, v);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (q + (W64.of_int 64))) (w);
    return ();
  }
}.

