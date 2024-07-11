require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array4.
require import WArray16.



module M = {
  proc f1 (r:W32.t Array4.t) : W32.t = {
    
    var res_0:W32.t;
    
    res_0 <- r.[0];
    return (res_0);
  }
  
  proc f2 (r1:W32.t Array4.t, r2:W32.t Array4.t) : W32.t = {
    
    var res_0:W32.t;
    var tmp:W32.t;
    
    res_0 <- r1.[0];
    tmp <- r2.[0];
    res_0 <- (res_0 + tmp);
    return (res_0);
  }
  
  proc f3 (r:W32.t Array4.t) : W32.t Array4.t = {
    
    var tmp:W32.t;
    
    tmp <- (W32.of_int 2);
    r.[0] <- tmp;
    return (r);
  }
  
  proc f4 (r1:W32.t Array4.t, r2:W32.t Array4.t, r3:W32.t Array4.t, x:W32.t) : 
  W32.t Array4.t * W32.t Array4.t = {
    
    var tmp:W32.t;
    
    r1.[0] <- x;
    tmp <- r3.[0];
    r2.[0] <- tmp;
    return (r1, r2);
  }
  
  proc f_copy (dst:W32.t Array4.t, src:W32.t Array4.t) : W32.t Array4.t = {
    
    
    
    dst <- copy_32 src;
    return (dst);
  }
}.

