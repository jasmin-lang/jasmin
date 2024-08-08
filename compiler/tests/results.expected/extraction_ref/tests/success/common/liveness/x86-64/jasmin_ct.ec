require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc inc (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a + (W32.of_int 1));
    a <- aux;
    return (a);
  }
  
  proc f1 (x:W32.t, y:W32.t) : W32.t = {
    var aux: W32.t;
    
    var v:W32.t;
    var t:W32.t;
    var u:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ inc (t);
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ inc (u);
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (v `^` y);
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (v `^` x);
    v <- aux;
    return (v);
  }
  
  proc f2 (z:W32.t) : W32.t * W32.t = {
    var aux: W32.t;
    
    var f:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ inc (f);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- f;
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    z <- aux;
    return (z, f);
  }
  
  proc leaf () : unit = {
    
    
    
    
    return ();
  }
  
  proc f3 (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    leaf ();
    return (a);
  }
  
  proc f4 (a:W32.t, b:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    leaf ();
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a `^` b);
    a <- aux;
    return (a);
  }
  
  proc bot () : unit = {
    
    
    
    
    return ();
  }
  
  proc mid () : W32.t = {
    var aux: W32.t;
    
    var q:W32.t;
    var p:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1);
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    bot ();
    leakages <- LeakAddr([]) :: leakages;
    aux <- p;
    q <- aux;
    leakages <- LeakAddr([]) :: leakages;
    bot ();
    leakages <- LeakAddr([]) :: leakages;
    aux <- (q `^` p);
    q <- aux;
    return (q);
  }
  
  proc top () : W32.t = {
    var aux: W32.t;
    
    var t:W32.t;
    var r:W32.t;
    var s:W32.t;
    var  _0:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    bot ();
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ mid ();
     _0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    bot ();
    return (t);
  }
}.

