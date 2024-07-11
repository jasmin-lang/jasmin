require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc xor64 (x:W256.t, i:int, c:W64.t) : W256.t = {
    
    var y:W128.t;
    var r:W64.t;
    
    y <- VEXTRACTI128 x (W8.of_int (i %/ 4));
    r <- VPEXTR_64 y (W8.of_int (i %% 4));
    r <- (r `^` c);
    y <- VPINSR_2u64 y r (W8.of_int (i %% 4));
    x <- VINSERTI128 x y (W8.of_int (i %/ 4));
    return (x);
  }
  
  proc test (p:W64.t) : unit = {
    
    var a:W256.t;
    
    a <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <@ xor64 (a, 1, (W64.of_int 12302652056653603379));
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (a);
    return ();
  }
}.

