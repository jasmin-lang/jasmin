require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.



abbrev c__A__x = W32.of_int 2.


abbrev c__x = W32.of_int 1.


module M = {
  proc a__id (x:W32.t) : W32.t = {
    
    
    
    x <- x;
    return (x);
  }
  
  proc b__id () : W32.t = {
    
    var i:W32.t;
    
    i <- (W32.of_int 42);
    return (i);
  }
  
  proc c__A__id () : W32.t = {
    
    var r:W32.t;
    
    r <- c__A__x;
    return (r);
  }
  
  proc main (a:W32.t) : W32.t = {
    
    var x:W32.t;
    var y:W32.t;
    var i:int;
    
    x <@ a__id (a);
    y <@ b__id ();
    x <- (x + y);
    i <- (W32.to_uint c__x);
    x <- (x + (W32.of_int i));
    i <- (W32.to_uint c__A__x);
    x <- (x + (W32.of_int i));
    y <@ c__A__id ();
    x <- (x + y);
    return (x);
  }
}.

