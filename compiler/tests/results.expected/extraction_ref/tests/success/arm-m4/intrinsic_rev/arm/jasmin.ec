require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc rev (x:W32.t) : W32.t = {
    
    var y:W32.t;
    var nf:bool;
    var zf:bool;
    var vf:bool;
    var cf:bool;
    
    y <- REV x;
    x <- REV16 y;
    y <- REVSH x;
    (nf, zf, vf, cf) <- CMP x y;
    y <- REVcc x cf y;
    x <- REV16cc y cf x;
    y <- REVSHcc x cf y;
    return (y);
  }
}.

