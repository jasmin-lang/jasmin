require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f8 (x:W8.t, y:W8.t) : W8.t = {
    
    var z:W8.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_8 x (W8.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCR_8 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc f16 (x:W16.t, y:W8.t) : W16.t = {
    
    var z:W16.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_16 x (W16.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCR_16 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc f32 (x:W32.t, y:W8.t) : W32.t = {
    
    var z:W32.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_32 x (W32.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCR_32 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc f64 (x:W64.t, y:W8.t) : W64.t = {
    
    var z:W64.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_64 x (W64.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCR_64 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc g8 (x:W8.t) : W8.t = {
    
    var z:W8.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_8 x (W8.of_int 1) false;
    (of_0, cf, x) <- RCR_8 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
  
  proc g16 (x:W16.t) : W16.t = {
    
    var z:W16.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_16 x (W16.of_int 1) false;
    (of_0, cf, x) <- RCR_16 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
  
  proc g32 (x:W32.t) : W32.t = {
    
    var z:W32.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_32 x (W32.of_int 1) false;
    (of_0, cf, x) <- RCR_32 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
  
  proc g64 (x:W64.t) : W64.t = {
    
    var z:W64.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_64 x (W64.of_int 1) false;
    (of_0, cf, x) <- RCR_64 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
  
  proc f8_ (x:W8.t, y:W8.t) : W8.t = {
    
    var z:W8.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_8 x (W8.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCL_8 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc f16_ (x:W16.t, y:W8.t) : W16.t = {
    
    var z:W16.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_16 x (W16.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCL_16 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc f32_ (x:W32.t, y:W8.t) : W32.t = {
    
    var z:W32.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_32 x (W32.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCL_32 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc f64_ (x:W64.t, y:W8.t) : W64.t = {
    
    var z:W64.t;
    var cf:bool;
    var y1:W8.t;
    var of_0:bool;
    
    (cf, x) <- adc_64 x (W64.of_int 1) false;
    y1 <- y;
    (of_0, cf, x) <- RCL_64 x y1 cf;
    z <- x;
    return (z);
  }
  
  proc g8_ (x:W8.t) : W8.t = {
    
    var z:W8.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_8 x (W8.of_int 1) false;
    (of_0, cf, x) <- RCL_8 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
  
  proc g16_ (x:W16.t) : W16.t = {
    
    var z:W16.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_16 x (W16.of_int 1) false;
    (of_0, cf, x) <- RCL_16 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
  
  proc g32_ (x:W32.t) : W32.t = {
    
    var z:W32.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_32 x (W32.of_int 1) false;
    (of_0, cf, x) <- RCL_32 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
  
  proc g64_ (x:W64.t) : W64.t = {
    
    var z:W64.t;
    var cf:bool;
    var of_0:bool;
    
    (cf, x) <- adc_64 x (W64.of_int 1) false;
    (of_0, cf, x) <- RCL_64 x (W8.of_int 3) cf;
    z <- x;
    return (z);
  }
}.

