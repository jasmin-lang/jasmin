require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (r1:W64.t, r2:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r1 <- (r1 + (W64.of_int 3));
    r1 <- ((W64.of_int 5) + r1);
    r1 <- ((W64.of_int 2) * r1);
    r1 <- ((W64.of_int 4) * r1);
    r1 <- ((W64.of_int 8) * r1);
    r1 <- ((W64.of_int 10) * r1);
    r1 <- (r1 * (W64.of_int 10));
    r1 <- (((W64.of_int 1) * r1) + r2);
    r1 <- (r1 * (W64.of_int 2));
    r1 <- (r1 * (W64.of_int 4));
    r1 <- (r1 * (W64.of_int 8));
    r1 <- ((r1 + r2) + (W64.of_int 7));
    r1 <- ((r1 + (W64.of_int 7)) + r2);
    r1 <- (((W64.of_int 7) + r1) + r2);
    r1 <- ((r1 + ((W64.of_int 2) * r2)) + (W64.of_int 10));
    r1 <- ((r1 + (W64.of_int 10)) + ((W64.of_int 2) * r2));
    r1 <- (((W64.of_int 10) + r1) + ((W64.of_int 2) * r2));
    r1 <- ((((W64.of_int 2) * r2) + r1) + (W64.of_int 10));
    r1 <- ((((W64.of_int 2) * r2) + (W64.of_int 10)) + r1);
    r1 <- (((W64.of_int 10) + ((W64.of_int 2) * r2)) + r1);
    r <- ((((W64.of_int 2) * (r1 + (W64.of_int 10))) + r2) + (W64.of_int 100));
    return (r);
  }
}.

