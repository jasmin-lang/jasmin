require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_if (msf:W64.t, x:W64.t) : W64.t = {
    
    var b:bool;
    
    b <- (x = (W64.of_int 0));
    if (b) {
      msf <- update_msf (! (! b)) msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    if (b) {
      msf <- update_msf b msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    if ((! b)) {
      msf <- update_msf (! b) msf;
    } else {
      msf <- update_msf b msf;
    }
    if ((! b)) {
      msf <- update_msf (! b) msf;
    } else {
      msf <- update_msf (! (! b)) msf;
    }
    b <- (x <> (W64.of_int 0));
    if (b) {
      msf <- update_msf (! (! b)) msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    if (b) {
      msf <- update_msf b msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    if ((! b)) {
      msf <- update_msf (! b) msf;
    } else {
      msf <- update_msf b msf;
    }
    if ((! b)) {
      msf <- update_msf (! b) msf;
    } else {
      msf <- update_msf (! (! b)) msf;
    }
    if ((true /\ b)) {
      msf <- update_msf b msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    if ((b /\ true)) {
      msf <- update_msf b msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    if (b) {
      msf <- update_msf (b \/ false) msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    return (msf);
  }
  
  proc test_while (msf:W64.t, x:W64.t) : W64.t = {
    
    var b:bool;
    
    b <- (x = (W64.of_int 0));
    
    while (b) {
      msf <- update_msf (! (! b)) msf;
    }
    msf <- update_msf (! b) msf;
    
    while (b) {
      msf <- update_msf b msf;
    }
    msf <- update_msf (! b) msf;
    
    while ((! b)) {
      msf <- update_msf (! b) msf;
    }
    msf <- update_msf b msf;
    
    while ((! b)) {
      msf <- update_msf (! b) msf;
    }
    msf <- update_msf (! (! b)) msf;
    b <- (x <> (W64.of_int 0));
    
    while (b) {
      msf <- update_msf (! (! b)) msf;
    }
    msf <- update_msf (! b) msf;
    
    while (b) {
      msf <- update_msf b msf;
    }
    msf <- update_msf (! b) msf;
    
    while ((! b)) {
      msf <- update_msf (! b) msf;
    }
    msf <- update_msf b msf;
    
    while ((! b)) {
      msf <- update_msf (! b) msf;
    }
    msf <- update_msf (! (! b)) msf;
    
    while ((true /\ b)) {
      msf <- update_msf b msf;
    }
    msf <- update_msf (! b) msf;
    
    while ((b /\ true)) {
      msf <- update_msf b msf;
    }
    msf <- update_msf (! b) msf;
    
    while (b) {
      msf <- update_msf (b \/ false) msf;
    }
    msf <- update_msf (! b) msf;
    return (msf);
  }
  
  proc main (a:W64.t) : W64.t = {
    
    var m:W64.t;
    
    m <- init_msf ;
    m <@ test_if (m, a);
    m <@ test_while (m, a);
    return (m);
  }
}.

