require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array2.
require import WArray2 WArray4.



module M = {
  var leakages : leakages_t
  
  proc main () : W32.t = {
    var aux_0: W8.t;
    var aux_1: W16.t;
    var aux: W32.t;
    
    var r:W32.t;
    var x:W32.t;
    var stk8:W8.t;
    var stk16:W16.t;
    var arr8:W8.t Array2.t;
    var arr16:W16.t Array2.t;
    var y:W32.t;
    arr16 <- witness;
    arr8 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    stk8 <- (truncateu8 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    stk16 <- (truncateu16 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    arr8.[0] <- (truncateu8 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([1]) :: leakages;
    arr8.[1] <- (truncateu8 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    arr16.[0] <- (truncateu16 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([1]) :: leakages;
    arr16.[1] <- (truncateu16 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu32 stk8);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (sigextu32 stk8);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + y);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu32 stk16);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (sigextu32 stk16);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + y);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (zeroextu32 arr8.[0]);
    x <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (sigextu32 arr8.[1]);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + y);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (zeroextu32 arr16.[0]);
    x <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (sigextu32 arr16.[1]);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + y);
    r <- aux;
    leakages <- LeakAddr([(W32.to_uint (r + (W32.of_int 0)))]) :: leakages;
    aux <- (zeroextu32 (loadW8 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (r + (W32.of_int 0)))]) :: leakages;
    aux <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + y);
    r <- aux;
    leakages <- LeakAddr([(W32.to_uint (r + (W32.of_int 0)))]) :: leakages;
    aux <- (zeroextu32 (loadW16 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    x <- aux;
    leakages <- LeakAddr([(W32.to_uint (r + (W32.of_int 0)))]) :: leakages;
    aux <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + y);
    r <- aux;
    return (r);
  }
}.

