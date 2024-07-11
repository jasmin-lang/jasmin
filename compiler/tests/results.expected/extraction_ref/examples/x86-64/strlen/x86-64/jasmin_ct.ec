require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc strlen (str:W64.t) : W8.t = {
    var aux: W8.t;
    var aux_0: W64.t;
    
    var len:W8.t;
    var c:W8.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int 0);
    len <- aux;
    leakages <- LeakAddr([(W64.to_uint (str + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW8 Glob.mem (W64.to_uint (str + (W64.of_int 0))));
    c <- aux;
    leakages <- LeakCond((c <> (W8.of_int 0))) :: LeakAddr([]) :: leakages;
    
    while ((c <> (W8.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (str + (W64.of_int 1));
      str <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (len + (W8.of_int 1));
      len <- aux;
      leakages <- LeakAddr([(W64.to_uint (str + (W64.of_int 0)))]) :: leakages;
      aux <- (loadW8 Glob.mem (W64.to_uint (str + (W64.of_int 0))));
      c <- aux;
    leakages <- LeakCond((c <> (W8.of_int 0))) :: LeakAddr([]) :: leakages;
    
    }
    return (len);
  }
  
  proc main (argc:W64.t, argv:W64.t) : W8.t = {
    var aux: W8.t;
    var aux_0: W64.t;
    
    var len:W8.t;
    var input:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int (- 1));
    len <- aux;
    leakages <- LeakCond((argc = (W64.of_int 2))) :: LeakAddr([]) :: leakages;
    if ((argc = (W64.of_int 2))) {
      leakages <- LeakAddr([(W64.to_uint (argv + (W64.of_int 8)))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (argv + (W64.of_int 8))));
      input <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ strlen (input);
      len <- aux;
    } else {
      
    }
    return (len);
  }
}.

