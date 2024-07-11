require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array2.
require import WArray1 WArray2.



module M = {
  var leakages : leakages_t
  
  proc id (x:W8.t Array1.t) : W8.t Array1.t = {
    var aux: W8.t;
    
    var v:W8.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (v + (W8.of_int 1));
    v <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- v;
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    return (x);
  }
  
  proc copy (y:W8.t Array2.t) : W8.t Array2.t = {
    var aux: W8.t Array1.t;
    
    
    
    leakages <- LeakAddr([(0 * 1)]) :: leakages;
    aux <@ id ((Array1.init (fun i => y.[(0 * 1) + i])));
    leakages <- LeakAddr([(0 * 1)]) :: leakages;
    y <- Array2.init (fun i => if (0 * 1) <= i < (0 * 1) + 1 then aux.[i-(0 * 1)] else y.[i]);
    leakages <- LeakAddr([(1 * 1)]) :: leakages;
    aux <@ id ((Array1.init (fun i => y.[(1 * 1) + i])));
    leakages <- LeakAddr([(1 * 1)]) :: leakages;
    y <- Array2.init (fun i => if (1 * 1) <= i < (1 * 1) + 1 then aux.[i-(1 * 1)] else y.[i]);
    return (y);
  }
  
  proc test (p:W64.t) : unit = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_5: int;
    var aux_4: W8.t;
    var aux_6: W8.t Array2.t;
    
    var z:W8.t;
    var i:int;
    var tab:W8.t Array2.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_8 ;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
     _4 <- aux;
    z <- aux_4;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_4 <- z;
      leakages <- LeakAddr([i]) :: leakages;
      tab.[i] <- aux_4;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <@ copy (tab);
    tab <- aux_6;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([0]) :: leakages;
      aux_4 <- tab.[0];
      z <- aux_4;
      leakages <- LeakAddr([]) :: leakages;
      aux_4 <- z;
      leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int i)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (p + (W64.of_int i))) (aux_4);
      i <- i + 1;
    }
    return ();
  }
}.

