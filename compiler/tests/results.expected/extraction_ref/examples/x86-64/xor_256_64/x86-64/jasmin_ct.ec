require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc xor64 (x:W256.t, i:int, c:W64.t) : W256.t = {
    var aux_0: W64.t;
    var aux: W128.t;
    var aux_1: W256.t;
    
    var y:W128.t;
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- VEXTRACTI128 x (W8.of_int (i %/ 4));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPEXTR_64 y (W8.of_int (i %% 4));
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (r `^` c);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPINSR_2u64 y r (W8.of_int (i %% 4));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- VINSERTI128 x y (W8.of_int (i %/ 4));
    x <- aux_1;
    return (x);
  }
  
  proc test (p:W64.t) : unit = {
    var aux: W256.t;
    
    var a:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ xor64 (a, 1, (W64.of_int 12302652056653603379));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
}.

