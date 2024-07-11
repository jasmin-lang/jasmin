require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc protect_init_msf_later (p:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var sum:W64.t;
    var msf:W64.t;
    var i:W64.t;
    var b:bool;
    var temp:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    sum <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (i \ult (W64.of_int 10));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (i \ult (W64.of_int 10));
    b <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    while (b) {
      leakages <- LeakAddr([(W64.to_uint (p + i))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (p + i)));
      temp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (sum + temp);
      sum <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W64.of_int 1));
      i <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i \ult (W64.of_int 10));
      b <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 sum msf;
    sum <- aux;
    return (sum);
  }
}.

