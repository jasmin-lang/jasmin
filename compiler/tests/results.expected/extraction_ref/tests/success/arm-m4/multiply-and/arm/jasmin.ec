require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc f (a:W32.t, b:W32.t, c:W32.t) : W32.t = {
    
    var d:W32.t;
    var cond:bool;
    
    cond <- (a = (W32.of_int 0));
    d <- ((a * b) + c);
    d <- (d + (b * c));
    a <- (cond ? ((b * c) + d) : a);
    a <- (cond ? (a + (b * c)) : a);
    b <- MLA c d a;
    c <- MLAcc d a b cond c;
    b <- (c - (d * a));
    b <- (b - (c * d));
    c <- (cond ? (d - (a * b)) : c);
    c <- (cond ? (c - (a * b)) : c);
    d <- MLS a b c;
    c <- MLScc d a b cond c;
    d <- c;
    return (d);
  }
}.

