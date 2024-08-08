require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_vpalignr_128 (cp:W64.t, ap:W64.t, bp:W64.t) : unit = {
    var aux: W128.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (ap + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (ap + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (bp + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (bp + (W64.of_int 0))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPALIGNR_128 a b (W8.of_int 8);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (cp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (cp + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_vpalignr_128_1 (cp:W64.t, ap:W64.t, bp:W64.t) : unit = {
    var aux: W128.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W128.t;
    
    leakages <- LeakAddr([(W64.to_uint (ap + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (ap + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (bp + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (bp + (W64.of_int 0))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPALIGNR_128 a b (W8.of_int 8);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (cp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (cp + (W64.of_int 0))) (aux);
    return ();
  }
  
  proc test_vpalignr_256 (cp:W64.t, ap:W64.t, bp:W64.t) : unit = {
    var aux: W256.t;
    
    var a:W256.t;
    var b:W256.t;
    var c:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (ap + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (ap + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (bp + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (bp + (W64.of_int 0))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPALIGNR_256 a b (W8.of_int 8);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    leakages <- LeakAddr([(W64.to_uint (cp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (cp + (W64.of_int 0))) (aux);
    return ();
  }
}.

