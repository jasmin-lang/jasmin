require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc inc (a:W32.t) : W32.t = {
    
    
    
    a <- (a + (W32.of_int 1));
    return (a);
  }
  
  proc f1 (x:W32.t, y:W32.t) : W32.t = {
    
    var v:W32.t;
    var t:W32.t;
    var u:W32.t;
    
    t <- x;
    u <@ inc (t);
    v <@ inc (u);
    v <- (v `^` y);
    v <- (v `^` x);
    return (v);
  }
  
  proc f2 (z:W32.t) : W32.t * W32.t = {
    
    var f:W32.t;
    
    f <- z;
    f <@ inc (f);
    f <- f;
    z <- z;
    return (z, f);
  }
  
  proc leaf () : unit = {
    
    
    
    
    return ();
  }
  
  proc f3 (a:W32.t) : W32.t = {
    
    
    
    a <- a;
    leaf ();
    return (a);
  }
  
  proc f4 (a:W32.t, b:W32.t) : W32.t = {
    
    
    
    a <- a;
    leaf ();
    a <- (a `^` b);
    return (a);
  }
  
  proc bot () : unit = {
    
    
    
    
    return ();
  }
  
  proc mid () : W32.t = {
    
    var q:W32.t;
    var p:W32.t;
    
    p <- (W32.of_int 1);
    bot ();
    q <- p;
    bot ();
    q <- (q `^` p);
    return (q);
  }
  
  proc top () : W32.t = {
    
    var t:W32.t;
    var r:W32.t;
    var s:W32.t;
    var  _0:W32.t;
    
    r <- (W32.of_int 1);
    bot ();
    s <- r;
     _0 <@ mid ();
    t <- s;
    bot ();
    return (t);
  }
}.

