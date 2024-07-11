require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc no_speculation () : W64.t = {
    var aux: W64.t;
    
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x <- aux;
    return (x);
  }
  
  proc main_no_spec (x:W64.t) : unit = {
    var aux: W64.t;
    
    var msf:W64.t;
    var y:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ no_speculation ();
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc id_msf (msf:W64.t) : W64.t = {
    
    
    
    
    return (msf);
  }
  
  proc main_id (x:W64.t) : unit = {
    var aux: W64.t;
    
    var msf:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ id_msf (msf);
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc my_mov_msf (msf:W64.t) : W64.t = {
    var aux: W64.t;
    
    var msf1:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- mov_msf msf;
    msf1 <- aux;
    return (msf1);
  }
  
  proc main_move (x:W64.t) : unit = {
    var aux: W64.t;
    
    var msf:W64.t;
    var msf1:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ my_mov_msf (msf);
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ my_mov_msf (msf);
    msf1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf1;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc dup_msf (msf:W64.t) : W64.t * W64.t = {
    var aux: W64.t;
    
    var msf1:W64.t;
    var msf2:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- mov_msf msf;
    msf1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- mov_msf msf;
    msf2 <- aux;
    return (msf1, msf2);
  }
  
  proc main_dup (x:W64.t) : unit = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var msf:W64.t;
    var msf1:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- init_msf ;
    msf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ dup_msf (msf);
    msf <- aux_0;
    msf1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- protect_64 x msf;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- protect_64 x msf1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux_0);
    return ();
  }
}.

