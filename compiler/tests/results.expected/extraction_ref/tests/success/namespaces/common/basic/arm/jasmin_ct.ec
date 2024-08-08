require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.

abbrev c__A__x = W32.of_int 2.


abbrev c__x = W32.of_int 1.


module M = {
  var leakages : leakages_t
  
  proc a__id (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    return (x);
  }
  
  proc b__id () : W32.t = {
    var aux: W32.t;
    
    var i:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 42);
    i <- aux;
    return (i);
  }
  
  proc c__A__id () : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- c__A__x;
    r <- aux;
    return (r);
  }
  
  proc main (a:W32.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var x:W32.t;
    var y:W32.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ a__id (a);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ b__id ();
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.to_uint c__x);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + (W32.of_int i));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.to_uint c__A__x);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + (W32.of_int i));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ c__A__id ();
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    x <- aux;
    return (x);
  }
}.

