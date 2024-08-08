require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc add (x:W64.t, y:W64.t) : W64.t = {
    
    var z:W64.t;
    
    z <- (x + y);
    return (z);
  }
  
  proc addc (x:W64.t, y:W64.t) : bool * W64.t = {
    
    var c:bool;
    var z:W64.t;
    
    (c, z) <- adc_64 x y false;
    return (c, z);
  }
  
  proc main () : W64.t = {
    
    var z:W64.t;
    var c:bool;
    
    (c, z) <@ addc ((W64.of_int 0), (W64.of_int 0));
    z <@ add ((W64.of_int 0), z);
    return (z);
  }
}.

