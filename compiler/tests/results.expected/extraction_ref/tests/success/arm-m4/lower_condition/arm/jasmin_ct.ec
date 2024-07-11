require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (x:W32.t, y:W32.t) : W32.t = {
    var aux: W32.t;
    
    var res_0:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x = y) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x = (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x <> y) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x <> (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \ult y) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \ult (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \slt y) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \slt (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \ule y) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \ule (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \sle y) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x \sle (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \ult x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((W32.of_int 6) \ult x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \slt x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((W32.of_int 6) \slt x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \ule x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((W32.of_int 6) \ule x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \sle x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((W32.of_int 6) \sle x) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((x `&` y) = (W32.of_int 0)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (((x `&` (W32.of_int 6)) = (W32.of_int 0)) ? (W32.of_int 1) : res_0);
    res_0 <- aux;
    leakages <- LeakCond((x = y)) :: LeakAddr([]) :: leakages;
    if ((x = y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x = (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    if ((x = (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x <> y)) :: LeakAddr([]) :: leakages;
    if ((x <> y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x <> (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    if ((x <> (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \ult y)) :: LeakAddr([]) :: leakages;
    if ((x \ult y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \ult (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    if ((x \ult (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \slt y)) :: LeakAddr([]) :: leakages;
    if ((x \slt y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \slt (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    if ((x \slt (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \ule y)) :: LeakAddr([]) :: leakages;
    if ((x \ule y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \ule (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    if ((x \ule (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \sle y)) :: LeakAddr([]) :: leakages;
    if ((x \sle y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \sle (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    if ((x \sle (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \ult x)) :: LeakAddr([]) :: leakages;
    if ((y \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond(((W32.of_int 6) \ult x)) :: LeakAddr([]) :: leakages;
    if (((W32.of_int 6) \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \slt x)) :: LeakAddr([]) :: leakages;
    if ((y \slt x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond(((W32.of_int 6) \slt x)) :: LeakAddr([]) :: leakages;
    if (((W32.of_int 6) \slt x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \ule x)) :: LeakAddr([]) :: leakages;
    if ((y \ule x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond(((W32.of_int 6) \ule x)) :: LeakAddr([]) :: leakages;
    if (((W32.of_int 6) \ule x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \sle x)) :: LeakAddr([]) :: leakages;
    if ((y \sle x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond(((W32.of_int 6) \sle x)) :: LeakAddr([]) :: leakages;
    if (((W32.of_int 6) \sle x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond(((x `&` y) = (W32.of_int 0))) :: LeakAddr([]) :: leakages;
    if (((x `&` y) = (W32.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    leakages <- LeakCond(((x `&` (W32.of_int 6)) = (W32.of_int 0))) :: LeakAddr(
    []) :: leakages;
    if (((x `&` (W32.of_int 6)) = (W32.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    } else {
      
    }
    
    leakages <- LeakCond((x = y)) :: LeakAddr([]) :: leakages;
    
    while ((x = y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x = y)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x = (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    while ((x = (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x = (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x <> y)) :: LeakAddr([]) :: leakages;
    
    while ((x <> y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x <> y)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x <> (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    while ((x <> (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x <> (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \ult y)) :: LeakAddr([]) :: leakages;
    
    while ((x \ult y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \ult y)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \ult (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    while ((x \ult (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \ult (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \slt y)) :: LeakAddr([]) :: leakages;
    
    while ((x \slt y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \slt y)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \slt (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    while ((x \slt (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \slt (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \ule y)) :: LeakAddr([]) :: leakages;
    
    while ((x \ule y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \ule y)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \ule (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    while ((x \ule (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \ule (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \sle y)) :: LeakAddr([]) :: leakages;
    
    while ((x \sle y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \sle y)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((x \sle (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    while ((x \sle (W32.of_int 6))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((x \sle (W32.of_int 6))) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((y \ult x)) :: LeakAddr([]) :: leakages;
    
    while ((y \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((y \ult x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond(((W32.of_int 6) \ult x)) :: LeakAddr([]) :: leakages;
    
    while (((W32.of_int 6) \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond(((W32.of_int 6) \ult x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((y \slt x)) :: LeakAddr([]) :: leakages;
    
    while ((y \slt x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((y \slt x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond(((W32.of_int 6) \slt x)) :: LeakAddr([]) :: leakages;
    
    while (((W32.of_int 6) \slt x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond(((W32.of_int 6) \slt x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((y \ule x)) :: LeakAddr([]) :: leakages;
    
    while ((y \ule x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((y \ule x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond(((W32.of_int 6) \ule x)) :: LeakAddr([]) :: leakages;
    
    while (((W32.of_int 6) \ule x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond(((W32.of_int 6) \ule x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond((y \sle x)) :: LeakAddr([]) :: leakages;
    
    while ((y \sle x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond((y \sle x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond(((W32.of_int 6) \sle x)) :: LeakAddr([]) :: leakages;
    
    while (((W32.of_int 6) \sle x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond(((W32.of_int 6) \sle x)) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond(((x `&` y) = (W32.of_int 0))) :: LeakAddr([]) :: leakages;
    
    while (((x `&` y) = (W32.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond(((x `&` y) = (W32.of_int 0))) :: LeakAddr([]) :: leakages;
    
    }
    
    leakages <- LeakCond(((x `&` (W32.of_int 6)) = (W32.of_int 0))) :: LeakAddr(
    []) :: leakages;
    
    while (((x `&` (W32.of_int 6)) = (W32.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 1);
      res_0 <- aux;
    leakages <- LeakCond(((x `&` (W32.of_int 6)) = (W32.of_int 0))) :: LeakAddr(
    []) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- res_0;
    res_0 <- aux;
    return (res_0);
  }
}.

