require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc strlen (str:W64.t) : W8.t = {
    
    var len:W8.t;
    var c:W8.t;
    
    len <- (W8.of_int 0);
    c <- (loadW8 Glob.mem (W64.to_uint (str + (W64.of_int 0))));
    while ((c <> (W8.of_int 0))) {
      str <- (str + (W64.of_int 1));
      len <- (len + (W8.of_int 1));
      c <- (loadW8 Glob.mem (W64.to_uint (str + (W64.of_int 0))));
    }
    return (len);
  }
  
  proc main (argc:W64.t, argv:W64.t) : W8.t = {
    
    var len:W8.t;
    var input:W64.t;
    
    len <- (W8.of_int (- 1));
    if ((argc = (W64.of_int 2))) {
      input <- (loadW64 Glob.mem (W64.to_uint (argv + (W64.of_int 8))));
      len <@ strlen (input);
    } else {
      
    }
    return (len);
  }
}.

