require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array3.
require import WArray1 WArray48.



module M = {
  var leakages : leakages_t
  
  proc test (x:W64.t) : W8.t = {
    var aux: W8.t;
    var aux_0: W64.t;
    var aux_1: W128.t;
    
    var b:W8.t;
    var a:W8.t Array1.t;
    var r:W128.t;
    var s:W128.t;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- (truncateu8 aux_0);
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    aux_1 <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))));
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- r;
    s <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- s;
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- r;
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux_1);
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    b <- aux;
    return (b);
  }
  
  proc test1 (x:W64.t) : unit = {
    var aux_2: int;
    var aux_3: W8.t;
    var aux_1: W32.t;
    var aux_0: W64.t;
    var aux: W128.t;
    
    var lll:W128.t;
    var a:W128.t Array3.t;
    var ll:W64.t;
    var l:W32.t;
    var i:int;
    var b:W8.t;
    a <- witness;
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))));
    lll <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- lll;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 16)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 16))));
    lll <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- lll;
    leakages <- LeakAddr([1]) :: leakages;
    a.[1] <- aux;
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (x + (W64.of_int 32))));
    ll <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ll;
    leakages <- LeakAddr([4]) :: leakages;
    a <- Array3.init (WArray48.get128 (WArray48.set64 (WArray48.init128 (fun i_0 => (a).[i_0])) 4 (aux_0)));
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 40)))]) :: leakages;
    aux_1 <- (loadW32 Glob.mem (W64.to_uint (x + (W64.of_int 40))));
    l <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- l;
    leakages <- LeakAddr([10]) :: leakages;
    a <- Array3.init (WArray48.get128 (WArray48.set32 (WArray48.init128 (fun i_0 => (a).[i_0])) 10 (aux_1)));
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 44)))]) :: leakages;
    aux_1 <- (loadW32 Glob.mem (W64.to_uint (x + (W64.of_int 44))));
    l <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- l;
    leakages <- LeakAddr([11]) :: leakages;
    a <- Array3.init (WArray48.get128 (WArray48.set32 (WArray48.init128 (fun i_0 => (a).[i_0])) 11 (aux_1)));
    leakages <- LeakFor(0,48) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 48) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_3 <- (get8 (WArray48.init128 (fun i_0 => (a).[i_0])) i);
      b <- aux_3;
      leakages <- LeakAddr([]) :: leakages;
      aux_3 <- b;
      leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int i)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (x + (W64.of_int i))) (aux_3);
      i <- i + 1;
    }
    return ();
  }
}.

