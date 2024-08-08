require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4 Array16.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc f1 (r:W32.t Array4.t) : W32.t = {
    var aux: W32.t;
    
    var res_0:W32.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- r.[0];
    res_0 <- aux;
    return (res_0);
  }
  
  proc f2 (r1:W32.t Array4.t, r2:W32.t Array4.t) : W32.t = {
    var aux: W32.t;
    
    var res_0:W32.t;
    var tmp:W32.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- r1.[0];
    res_0 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- r2.[0];
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (res_0 + tmp);
    res_0 <- aux;
    return (res_0);
  }
  
  proc f3 (r:W32.t Array4.t) : W32.t Array4.t = {
    var aux: W32.t;
    
    var tmp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 2);
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- tmp;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    return (r);
  }
  
  proc f4 (r1:W32.t Array4.t, r2:W32.t Array4.t, r3:W32.t Array4.t, x:W32.t) : 
  W32.t Array4.t * W32.t Array4.t = {
    var aux: W32.t;
    
    var tmp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    r1.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- r3.[0];
    tmp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- tmp;
    leakages <- LeakAddr([0]) :: leakages;
    r2.[0] <- aux;
    return (r1, r2);
  }
  
  proc f_copy (dst:W32.t Array4.t, src:W32.t Array4.t) : W32.t Array4.t = {
    var aux: W8.t Array16.t;
    var aux_0: W32.t Array4.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 src;
    dst <- aux_0;
    return (dst);
  }
}.

