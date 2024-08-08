require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test () : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var x:W64.t;
    var y:W64.t;
    var z:W64.t;
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + (W64.of_int 420));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + (W64.of_int 737894400000));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y - (W64.of_int (- 2147483648)));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y - (W64.of_int 2147483647));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- sbb_64 y (W64.of_int 20015998348237) false;
    cf <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 z (W64.of_int 42) cf;
    cf <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 z (W64.of_int (- 2147483649)) cf;
    cf <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- sbb_64 z (W64.of_int 0) cf;
    cf <- aux_0;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x * (W64.of_int 12));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (z * (W64.of_int (- 2147483650)));
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `|` (W64.of_int 33));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y `|` (W64.of_int 737894400000));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (z `^` (W64.of_int (- 1)));
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` (W64.of_int 2147483648));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y `&` (W64.of_int (- 2147483648)));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (z `&` (W64.of_int 737894400000));
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r `&` x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r `&` y);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r `&` z);
    r <- aux;
    return (r);
  }
}.

