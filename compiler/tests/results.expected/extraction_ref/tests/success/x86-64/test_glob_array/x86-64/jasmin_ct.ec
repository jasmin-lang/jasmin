require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4 Array9.
require import WArray32 WArray36.

abbrev glob_t = Array4.of_list witness [W64.of_int 0; W64.of_int 1; W64.of_int 2; W64.of_int 3].


abbrev t32 = Array9.of_list witness [W32.of_int 4; W32.of_int 0; W32.of_int 5; W32.of_int 0; W32.of_int 6; W32.of_int 0; W32.of_int 7; W32.of_int 0; W32.of_int 8].


module M = {
  var leakages : leakages_t
  
  proc sum (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + glob_t.[0]);
    r <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (r + glob_t.[1]);
    r <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (r + glob_t.[2]);
    r <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (r + glob_t.[3]);
    r <- aux;
    return (r);
  }
  
  proc sum1 (x:W64.t) : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var r:W64.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (r + glob_t.[i]);
      r <- aux;
      i <- i + 1;
    }
    return (r);
  }
  
  proc sum32 (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 0));
    r <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 1));
    r <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 2));
    r <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 3));
    r <- aux;
    return (r);
  }
  
  proc suma (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + t32.[0]);
    r <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (r + t32.[1]);
    r <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (r + t32.[2]);
    r <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (r + t32.[3]);
    r <- aux;
    return (r);
  }
}.

