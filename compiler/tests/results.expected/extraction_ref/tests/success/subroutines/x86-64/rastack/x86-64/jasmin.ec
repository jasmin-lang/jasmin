require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc copy (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var t:W64.t;
    
    t <- x;
    r <- t;
    return (r);
  }
  
  proc main (arg:W64.t) : W64.t = {
    
    var result:W64.t;
    
    result <@ copy (arg);
    return (result);
  }
  
  proc copy32 (x:W32.t) : W32.t = {
    
    var r:W32.t;
    var t:W32.t;
    
    t <- x;
    r <- t;
    return (r);
  }
  
  proc main32 (arg:W32.t) : W32.t = {
    
    var result:W32.t;
    
    result <@ copy32 (arg);
    return (result);
  }
  
  proc copy32_32 (x:W32.t) : W32.t = {
    
    var r:W32.t;
    var t:W32.t;
    
    t <- x;
    r <- t;
    return (r);
  }
  
  proc main32_32 (arg:W32.t) : W32.t = {
    
    var result:W32.t;
    
    result <@ copy32_32 (arg);
    return (result);
  }
  
  proc copy128 (x:W128.t) : W128.t = {
    
    var r:W128.t;
    var t:W128.t;
    var q:W32.t;
    var w:W128.t;
    
    t <- x;
    q <- (W32.of_int 0);
    r <- MOVD_32 q;
    w <- t;
    r <- (r \vadd32u128 w);
    return (r);
  }
  
  proc main128 (arg:W128.t) : W128.t = {
    
    var result:W128.t;
    
    result <@ copy128 (arg);
    return (result);
  }
}.

