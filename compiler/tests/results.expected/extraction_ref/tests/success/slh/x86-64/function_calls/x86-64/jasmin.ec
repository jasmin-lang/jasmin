require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc no_speculation () : W64.t = {
    
    var x:W64.t;
    
    x <- (W64.of_int 0);
    return (x);
  }
  
  proc main_no_spec (x:W64.t) : unit = {
    
    var msf:W64.t;
    var y:W64.t;
    
    msf <- init_msf ;
    y <@ no_speculation ();
    x <- (x + y);
    x <- protect_64 x msf;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) ((W64.of_int 0));
    return ();
  }
  
  proc id_msf (msf:W64.t) : W64.t = {
    
    
    
    
    return (msf);
  }
  
  proc main_id (x:W64.t) : unit = {
    
    var msf:W64.t;
    
    msf <- init_msf ;
    msf <@ id_msf (msf);
    x <- protect_64 x msf;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) ((W64.of_int 0));
    return ();
  }
  
  proc my_mov_msf (msf:W64.t) : W64.t = {
    
    var msf1:W64.t;
    
    msf1 <- mov_msf msf;
    return (msf1);
  }
  
  proc main_move (x:W64.t) : unit = {
    
    var msf:W64.t;
    var msf1:W64.t;
    
    msf <- init_msf ;
    msf <@ my_mov_msf (msf);
    x <- protect_64 x msf;
    msf1 <@ my_mov_msf (msf);
    x <- protect_64 x msf1;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) ((W64.of_int 0));
    return ();
  }
  
  proc dup_msf (msf:W64.t) : W64.t * W64.t = {
    
    var msf1:W64.t;
    var msf2:W64.t;
    
    msf1 <- mov_msf msf;
    msf2 <- mov_msf msf;
    return (msf1, msf2);
  }
  
  proc main_dup (x:W64.t) : unit = {
    
    var msf:W64.t;
    var msf1:W64.t;
    
    msf <- init_msf ;
    (msf, msf1) <@ dup_msf (msf);
    x <- protect_64 x msf;
    x <- protect_64 x msf1;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) ((W64.of_int 0));
    return ();
  }
}.

