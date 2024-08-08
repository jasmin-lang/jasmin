require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (p:W64.t) : unit = {
    var aux: W64.t;
    
    var s:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc main0 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main1 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main2 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main3 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main4 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main5 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main6 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main7 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main8 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main9 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main10 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main11 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main12 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
  
  proc main13 (p:W64.t) : unit = {
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    f (p);
    return ();
  }
}.

