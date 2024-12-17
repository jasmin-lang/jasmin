require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_m4.

import SLH32.

require import
Array4 Array8 Array16 Array32 Array64 WArray64 WArray256 BArray64 BArray256
SBArray256_64.

module M = {
  proc store (a:BArray64.t) : BArray64.t = {

    a <- (BArray64.set64 a 0 (W64.of_int 0));
    a <- (BArray64.set8 a 0 (W8.of_int 0));
    a <- (BArray64.set32 a 0 (W32.of_int 0));
    a <- (BArray64.set64 a 0 (W64.of_int 0));
    a <- (BArray64.set128 a 0 (W128.of_int 0));
    a <- (BArray64.set256 a 0 (W256.of_int 0));
    a <- (BArray64.set64d a 0 (W64.of_int 0));
    a <- (BArray64.set8d a 0 (W8.of_int 0));
    a <- (BArray64.set32d a 0 (W32.of_int 0));
    a <- (BArray64.set64d a 0 (W64.of_int 0));
    a <- (BArray64.set128d a 0 (W128.of_int 0));
    a <- (BArray64.set256d a 0 (W256.of_int 0));
    return a;
  }
  proc load (a:BArray64.t) : BArray64.t = {
    var x8:W8.t;
    var x16:W16.t;
    var x32:W32.t;
    var x64:W64.t;
    var x128:W128.t;
    var x256:W256.t;
    x8 <- (BArray64.get8 a 0);
    x16 <- (BArray64.get16 a 0);
    x32 <- (BArray64.get32 a 0);
    x64 <- (BArray64.get64 a 0);
    x128 <- (BArray64.get128 a 0);
    x256 <- (BArray64.get256 a 0);
    x8 <- (BArray64.get8d a 0);
    x16 <- (BArray64.get16d a 0);
    x32 <- (BArray64.get32d a 0);
    x64 <- (BArray64.get64d a 0);
    x128 <- (BArray64.get128d a 0);
    x256 <- (BArray64.get256d a 0);
    return a;
  }
  proc sub (a:BArray256.t) : BArray256.t = {
    var aux:BArray64.t;
    var i:int;
    i <- 0;
    while ((i < 4)) {
      aux <@ store ((SBArray256_64.get_sub32 a i));
      a <- (SBArray256_64.set_sub32 a i aux);
      aux <@ store ((SBArray256_64.get_sub16 a ((i * 2) * 2)));
      a <- (SBArray256_64.set_sub1 a ((i * 2) * 32) aux);
      aux <@ store ((SBArray256_64.get_sub32 a ((i * 2) * 1)));
      a <- (SBArray256_64.set_sub2 a ((i * 2) * 16) aux);
      aux <@ store ((SBArray256_64.get_sub1 a ((i * 2) * 32)));
      a <- (SBArray256_64.set_sub4 a ((i * 2) * 8) aux);
      aux <@ store ((SBArray256_64.get_sub2 a ((i * 2) * 16)));
      a <- (SBArray256_64.set_sub8 a ((i * 2) * 4) aux);
      aux <@ store ((SBArray256_64.get_sub4 a ((i * 2) * 8)));
      a <- (SBArray256_64.set_sub16 a ((i * 2) * 2) aux);
      aux <@ store ((SBArray256_64.get_sub8 a ((i * 2) * 4)));
      a <- (SBArray256_64.set_sub32 a ((i * 2) * 1) aux);
      aux <@ store ((SBArray256_64.get_sub32 a i));
      a <- (SBArray256_64.set_sub a i aux);
      aux <@ store ((SBArray256_64.get_sub a ((i * 2) * 2)));
      a <- (SBArray256_64.set_sub a ((i * 2) * 32) aux);
      aux <@ store ((SBArray256_64.get_sub a ((i * 2) * 1)));
      a <- (SBArray256_64.set_sub a ((i * 2) * 16) aux);
      aux <@ store ((SBArray256_64.get_sub a ((i * 2) * 32)));
      a <- (SBArray256_64.set_sub a ((i * 2) * 8) aux);
      aux <@ store ((SBArray256_64.get_sub a ((i * 2) * 16)));
      a <- (SBArray256_64.set_sub a ((i * 2) * 4) aux);
      aux <@ store ((SBArray256_64.get_sub a ((i * 2) * 8)));
      a <- (SBArray256_64.set_sub a ((i * 2) * 2) aux);
      aux <@ store ((SBArray256_64.get_sub a ((i * 2) * 4)));
      a <- (SBArray256_64.set_sub a ((i * 2) * 1) aux);
      i <- (i + 1);
    }
    return a;
  }
  proc g (a:BArray64.t) : BArray64.t = {
    var aux:BArray64.t;
    aux <@ store (a);
    a <- aux;
    aux <@ load (a);
    a <- aux;
    return a;
  }
}.
