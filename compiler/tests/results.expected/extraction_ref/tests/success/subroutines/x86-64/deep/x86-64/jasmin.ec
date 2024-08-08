require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f5 (x:W64.t) : W64.t = {
    
    
    
    
    return (x);
  }
  
  proc f4 (x:W64.t) : W64.t = {
    
    
    
    x <@ f5 (x);
    return (x);
  }
  
  proc f3 (x:W64.t) : W64.t = {
    
    
    
    x <@ f4 (x);
    return (x);
  }
  
  proc f2 (x:W64.t) : W64.t = {
    
    
    
    x <@ f3 (x);
    return (x);
  }
  
  proc f1 (x:W64.t) : W64.t = {
    
    
    
    x <@ f2 (x);
    return (x);
  }
  
  proc main (a:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- a;
    r <@ f1 (r);
    return (r);
  }
}.

