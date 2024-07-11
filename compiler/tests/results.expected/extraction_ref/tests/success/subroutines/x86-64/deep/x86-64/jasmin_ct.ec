require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f5 (x:W64.t) : W64.t = {
    
    
    
    
    return (x);
  }
  
  proc f4 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f5 (x);
    x <- aux;
    return (x);
  }
  
  proc f3 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f4 (x);
    x <- aux;
    return (x);
  }
  
  proc f2 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f3 (x);
    x <- aux;
    return (x);
  }
  
  proc f1 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f2 (x);
    x <- aux;
    return (x);
  }
  
  proc main (a:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f1 (r);
    r <- aux;
    return (r);
  }
}.

