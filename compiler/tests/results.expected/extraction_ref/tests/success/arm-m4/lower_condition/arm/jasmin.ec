require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc main (x:W32.t, y:W32.t) : W32.t = {
    
    var res_0:W32.t;
    
    res_0 <- (W32.of_int 0);
    res_0 <- ((x = y) ? (W32.of_int 1) : res_0);
    res_0 <- ((x = (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- ((x <> y) ? (W32.of_int 1) : res_0);
    res_0 <- ((x <> (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \ult y) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \ult (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \slt y) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \slt (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \ule y) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \ule (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \sle y) ? (W32.of_int 1) : res_0);
    res_0 <- ((x \sle (W32.of_int 6)) ? (W32.of_int 1) : res_0);
    res_0 <- ((y \ult x) ? (W32.of_int 1) : res_0);
    res_0 <- (((W32.of_int 6) \ult x) ? (W32.of_int 1) : res_0);
    res_0 <- ((y \slt x) ? (W32.of_int 1) : res_0);
    res_0 <- (((W32.of_int 6) \slt x) ? (W32.of_int 1) : res_0);
    res_0 <- ((y \ule x) ? (W32.of_int 1) : res_0);
    res_0 <- (((W32.of_int 6) \ule x) ? (W32.of_int 1) : res_0);
    res_0 <- ((y \sle x) ? (W32.of_int 1) : res_0);
    res_0 <- (((W32.of_int 6) \sle x) ? (W32.of_int 1) : res_0);
    res_0 <- (((x `&` y) = (W32.of_int 0)) ? (W32.of_int 1) : res_0);
    res_0 <- (((x `&` (W32.of_int 6)) = (W32.of_int 0)) ? (W32.of_int 1) : res_0);
    if ((x = y)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x = (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x <> y)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x <> (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \ult y)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \ult (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \slt y)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \slt (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \ule y)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \ule (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \sle y)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((x \sle (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((y \ult x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if (((W32.of_int 6) \ult x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((y \slt x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if (((W32.of_int 6) \slt x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((y \ule x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if (((W32.of_int 6) \ule x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if ((y \sle x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if (((W32.of_int 6) \sle x)) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if (((x `&` y) = (W32.of_int 0))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    if (((x `&` (W32.of_int 6)) = (W32.of_int 0))) {
      res_0 <- (W32.of_int 1);
    } else {
      
    }
    
    while ((x = y)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x = (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x <> y)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x <> (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \ult y)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \ult (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \slt y)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \slt (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \ule y)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \ule (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \sle y)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((x \sle (W32.of_int 6))) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((y \ult x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while (((W32.of_int 6) \ult x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((y \slt x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while (((W32.of_int 6) \slt x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((y \ule x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while (((W32.of_int 6) \ule x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while ((y \sle x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while (((W32.of_int 6) \sle x)) {
      res_0 <- (W32.of_int 1);
    }
    
    while (((x `&` y) = (W32.of_int 0))) {
      res_0 <- (W32.of_int 1);
    }
    
    while (((x `&` (W32.of_int 6)) = (W32.of_int 0))) {
      res_0 <- (W32.of_int 1);
    }
    res_0 <- res_0;
    return (res_0);
  }
}.

