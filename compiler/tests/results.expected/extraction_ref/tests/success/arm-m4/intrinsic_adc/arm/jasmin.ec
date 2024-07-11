require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc adc (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var c:bool;
    var x:W32.t;
    var n:bool;
    var z:bool;
    var v:bool;
    var _nf_:bool;
    var _zf_:bool;
    var _vf_:bool;
    var zf:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:W32.t;
    
    ( _0,  _1, c,  _2) <- MOVS arg0;
    x <- ADC arg0 arg1 c;
    x <- ADC x (W32.of_int 0) c;
    x <- ADC x (W32.of_int 1) c;
    x <- ADC x (W32.of_int 255) c;
    x <- ADC x (W32.of_int 3402287818) c;
    x <- ADC x (W32.of_int 3389049344) c;
    x <- ADC x (W32.of_int 13238474) c;
    x <- ADC x (W32.of_int 831488) c;
    x <- ADC x (arg0 `<<` (W8.of_int 0)) c;
    x <- ADC x (arg0 `<<` (W8.of_int 31)) c;
    x <- ADC x (arg0 `>>` (W8.of_int 1)) c;
    x <- ADC x (arg0 `>>` (W8.of_int 32)) c;
    x <- ADC x (arg0 `|>>` (W8.of_int 1)) c;
    x <- ADC x (arg0 `|>>` (W8.of_int 32)) c;
    x <- ADC x (arg0 `|>>|` (W8.of_int 1)) c;
    x <- ADC x (arg0 `|>>|` (W8.of_int 31)) c;
    (n, z, c, v, x) <- ADCS x arg0 c;
    (n, z, c, v, x) <- ADCS x (W32.of_int 1) c;
    (n, z, c, v, x) <- ADCS x (W32.of_int 3402287818) c;
    (n, z, c, v, x) <- ADCS x (W32.of_int 3389049344) c;
    (n, z, c, v, x) <- ADCS x (W32.of_int 13238474) c;
    (n, z, c, v, x) <- ADCS x (W32.of_int 831488) c;
    (n, z, c, v, x) <- ADCS x (arg0 `<<` (W8.of_int 3)) c;
    x <- ADCcc x arg0 c z x;
    x <- ADCcc x arg0 c (! z) x;
    x <- ADCcc x arg0 c c x;
    x <- ADCcc x arg0 c (! c) x;
    x <- ADCcc x arg0 c n x;
    x <- ADCcc x arg0 c (! n) x;
    x <- ADCcc x arg0 c v x;
    x <- ADCcc x arg0 c (! v) x;
    x <- ADCcc x arg0 c (c /\ (! z)) x;
    x <- ADCcc x arg0 c ((! c) \/ z) x;
    x <- ADCcc x arg0 c (n = v) x;
    x <- ADCcc x arg0 c (! (n = v)) x;
    x <- ADCcc x arg0 c ((! z) /\ (n = v)) x;
    x <- ADCcc x arg0 c (z \/ (! (n = v))) x;
    x <- ADCcc x (W32.of_int 1) c (! (! (! (! z)))) x;
    (n, z, c, v, x) <- ADCScc x arg0 c (n = v) n z c v x;
    (n, z, c, v, x) <- ADCScc x (W32.of_int 2) c ((! c) \/ z) n z c v x;
    x <- ADCcc x (arg0 `<<` (W8.of_int 3)) c z x;
    (n, z, c, v, x) <- ADCScc x (arg0 `<<` (W8.of_int 3)) c z n z c v x;
    (_nf_, _zf_, c, _vf_, x) <- ADCS x arg0 c;
    (_nf_, zf, c, _vf_, x) <- ADCS x arg0 c;
    (_nf_, _zf_, cf, _vf_, x) <- ADCS x arg0 c;
    res_0 <- x;
    return (res_0);
  }
}.

