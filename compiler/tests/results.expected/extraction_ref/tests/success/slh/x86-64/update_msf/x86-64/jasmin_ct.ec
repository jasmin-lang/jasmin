require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_if (msf:W64.t, x:W64.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x = (W64.of_int 0));
    b <- aux;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! (! b)) msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    }
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    }
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    if ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    }
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    if ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! (! b)) msf;
      msf <- aux_0;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x <> (W64.of_int 0));
    b <- aux;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! (! b)) msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    }
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    }
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    if ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    }
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    if ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! (! b)) msf;
      msf <- aux_0;
    }
    leakages <- LeakCond((true /\ b)) :: LeakAddr([]) :: leakages;
    if ((true /\ b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    }
    leakages <- LeakCond((b /\ true)) :: LeakAddr([]) :: leakages;
    if ((b /\ true)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    }
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (b \/ false) msf;
      msf <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    }
    return (msf);
  }
  
  proc test_while (msf:W64.t, x:W64.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x = (W64.of_int 0));
    b <- aux;
    
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    while (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! (! b)) msf;
      msf <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! b) msf;
    msf <- aux_0;
    
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    while (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! b) msf;
    msf <- aux_0;
    
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    while ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf b msf;
    msf <- aux_0;
    
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    while ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! (! b)) msf;
    msf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x <> (W64.of_int 0));
    b <- aux;
    
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    while (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! (! b)) msf;
      msf <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! b) msf;
    msf <- aux_0;
    
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    while (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! b) msf;
    msf <- aux_0;
    
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    while ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf b msf;
    msf <- aux_0;
    
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    while ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (! b) msf;
      msf <- aux_0;
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! (! b)) msf;
    msf <- aux_0;
    
    leakages <- LeakCond((true /\ b)) :: LeakAddr([]) :: leakages;
    
    while ((true /\ b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    leakages <- LeakCond((true /\ b)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! b) msf;
    msf <- aux_0;
    
    leakages <- LeakCond((b /\ true)) :: LeakAddr([]) :: leakages;
    
    while ((b /\ true)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf b msf;
      msf <- aux_0;
    leakages <- LeakCond((b /\ true)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! b) msf;
    msf <- aux_0;
    
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    while (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- update_msf (b \/ false) msf;
      msf <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- update_msf (! b) msf;
    msf <- aux_0;
    return (msf);
  }
  
  proc main (a:W64.t) : W64.t = {
    var aux: W64.t;
    
    var m:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    m <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test_if (m, a);
    m <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test_while (m, a);
    m <- aux;
    return (m);
  }
}.

