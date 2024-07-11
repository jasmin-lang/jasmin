require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc copy (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var t:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    r <- aux;
    return (r);
  }
  
  proc main (arg:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy (arg);
    result <- aux;
    return (result);
  }
  
  proc copy32 (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    var t:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    r <- aux;
    return (r);
  }
  
  proc main32 (arg:W32.t) : W32.t = {
    var aux: W32.t;
    
    var result:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy32 (arg);
    result <- aux;
    return (result);
  }
  
  proc copy32_32 (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    var t:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    r <- aux;
    return (r);
  }
  
  proc main32_32 (arg:W32.t) : W32.t = {
    var aux: W32.t;
    
    var result:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy32_32 (arg);
    result <- aux;
    return (result);
  }
  
  proc copy128 (x:W128.t) : W128.t = {
    var aux_0: W32.t;
    var aux: W128.t;
    
    var r:W128.t;
    var t:W128.t;
    var q:W32.t;
    var w:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    q <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOVD_32 q;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    w <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r \vadd32u128 w);
    r <- aux;
    return (r);
  }
  
  proc main128 (arg:W128.t) : W128.t = {
    var aux: W128.t;
    
    var result:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ copy128 (arg);
    result <- aux;
    return (result);
  }
}.

