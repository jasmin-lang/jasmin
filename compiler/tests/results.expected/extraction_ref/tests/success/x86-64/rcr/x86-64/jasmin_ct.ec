require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f8 (x:W8.t, y:W8.t) : W8.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W8.t;
    
    var z:W8.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_8 x (W8.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    y1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCR_8 x y1 cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc f16 (x:W16.t, y:W8.t) : W16.t = {
    var aux_2: bool;
    var aux: bool;
    var aux_1: W8.t;
    var aux_0: W16.t;
    
    var z:W16.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_0) <- adc_16 x (W16.of_int 1) false;
    cf <- aux_2;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- y;
    y1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux, aux_0) <- RCR_16 x y1 cf;
    of_0 <- aux_2;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc f32 (x:W32.t, y:W8.t) : W32.t = {
    var aux_2: bool;
    var aux: bool;
    var aux_1: W8.t;
    var aux_0: W32.t;
    
    var z:W32.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_0) <- adc_32 x (W32.of_int 1) false;
    cf <- aux_2;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- y;
    y1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux, aux_0) <- RCR_32 x y1 cf;
    of_0 <- aux_2;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc f64 (x:W64.t, y:W8.t) : W64.t = {
    var aux_2: bool;
    var aux: bool;
    var aux_1: W8.t;
    var aux_0: W64.t;
    
    var z:W64.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_0) <- adc_64 x (W64.of_int 1) false;
    cf <- aux_2;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- y;
    y1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux, aux_0) <- RCR_64 x y1 cf;
    of_0 <- aux_2;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g8 (x:W8.t) : W8.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W8.t;
    
    var z:W8.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_8 x (W8.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCR_8 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g16 (x:W16.t) : W16.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W16.t;
    
    var z:W16.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_16 x (W16.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCR_16 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g32 (x:W32.t) : W32.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W32.t;
    
    var z:W32.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_32 x (W32.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCR_32 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g64 (x:W64.t) : W64.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W64.t;
    
    var z:W64.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_64 x (W64.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCR_64 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc f8_ (x:W8.t, y:W8.t) : W8.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W8.t;
    
    var z:W8.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_8 x (W8.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    y1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCL_8 x y1 cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc f16_ (x:W16.t, y:W8.t) : W16.t = {
    var aux_2: bool;
    var aux: bool;
    var aux_1: W8.t;
    var aux_0: W16.t;
    
    var z:W16.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_0) <- adc_16 x (W16.of_int 1) false;
    cf <- aux_2;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- y;
    y1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux, aux_0) <- RCL_16 x y1 cf;
    of_0 <- aux_2;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc f32_ (x:W32.t, y:W8.t) : W32.t = {
    var aux_2: bool;
    var aux: bool;
    var aux_1: W8.t;
    var aux_0: W32.t;
    
    var z:W32.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_0) <- adc_32 x (W32.of_int 1) false;
    cf <- aux_2;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- y;
    y1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux, aux_0) <- RCL_32 x y1 cf;
    of_0 <- aux_2;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc f64_ (x:W64.t, y:W8.t) : W64.t = {
    var aux_2: bool;
    var aux: bool;
    var aux_1: W8.t;
    var aux_0: W64.t;
    
    var z:W64.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_0) <- adc_64 x (W64.of_int 1) false;
    cf <- aux_2;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- y;
    y1 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux, aux_0) <- RCL_64 x y1 cf;
    of_0 <- aux_2;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g8_ (x:W8.t) : W8.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W8.t;
    
    var z:W8.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_8 x (W8.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCL_8 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g16_ (x:W16.t) : W16.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W16.t;
    
    var z:W16.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_16 x (W16.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCL_16 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g32_ (x:W32.t) : W32.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W32.t;
    
    var z:W32.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_32 x (W32.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCL_32 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
  
  proc g64_ (x:W64.t) : W64.t = {
    var aux_1: bool;
    var aux: bool;
    var aux_0: W64.t;
    
    var z:W64.t;
    var cf:bool;
    var of_0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- adc_64 x (W64.of_int 1) false;
    cf <- aux_1;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux, aux_0) <- RCL_64 x (W8.of_int 3) cf;
    of_0 <- aux_1;
    cf <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    z <- aux_0;
    return (z);
  }
}.

