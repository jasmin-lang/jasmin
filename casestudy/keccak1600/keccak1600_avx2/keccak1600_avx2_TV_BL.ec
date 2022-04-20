require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.

require import Array7 Array9 Array28.
require import WArray224 WArray288.

abbrev g_zero = W64.of_int 0.

theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t
  
  proc __keccakf1600_avx2 (state:W256.t Array7.t, _rhotates_left:W64.t,
                           _rhotates_right:W64.t, _iotas:W64.t) : W256.t Array7.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_0: W32.t;
    var aux: W64.t;
    var aux_1: W256.t;
    
    var rhotates_left:W64.t;
    var rhotates_right:W64.t;
    var iotas:W64.t;
    var r:W32.t;
    var zf:bool;
    var c00:W256.t;
    var c14:W256.t;
    var t:W256.t Array9.t;
    var d14:W256.t;
    var d00:W256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    t <- witness;
    aux <- (_rhotates_left + (W64.of_int 96));
    rhotates_left <- aux;
    aux <- (_rhotates_right + (W64.of_int 96));
    rhotates_right <- aux;
    aux <- _iotas;
    iotas <- aux;
    aux_0 <- (W32.of_int 24);
    r <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- VPSHUFD_256 state.[2]
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
    c00 <- aux_1;
    leakages <- LeakAddr([3] ++ [5]) :: leakages;
    aux_1 <- (state.[5] `^` state.[3]);
    c14 <- aux_1;
    leakages <- LeakAddr([6] ++ [4]) :: leakages;
    aux_1 <- (state.[4] `^` state.[6]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- (c14 `^` state.[1]);
    c14 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- (c14 `^` t.[2]);
    c14 <- aux_1;
    aux_1 <- VPERMQ c14
    (W8.of_int (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- (c00 `^` state.[2]);
    c00 <- aux_1;
    aux_1 <- VPERMQ c00
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    aux_1 <- (c14 \vshr64u256 (W8.of_int 63));
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux_1;
    aux_1 <- (c14 \vadd64u256 c14);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux_1;
    leakages <- LeakAddr([2] ++ [1]) :: leakages;
    aux_1 <- (t.[1] `|` t.[2]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- VPERMQ t.[1]
    (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    d14 <- aux_1;
    leakages <- LeakAddr([4] ++ [1]) :: leakages;
    aux_1 <- (t.[1] `^` t.[4]);
    d00 <- aux_1;
    aux_1 <- VPERMQ d00
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    d00 <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- (c00 `^` state.[0]);
    c00 <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- (c00 `^` t.[0]);
    c00 <- aux_1;
    aux_1 <- (c00 \vshr64u256 (W8.of_int 63));
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    aux_1 <- (c00 \vadd64u256 c00);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux_1;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux_1 <- (t.[1] `|` t.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- (state.[2] `^` d00);
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- (state.[0] `^` d00);
    leakages <- LeakAddr([0]) :: leakages;
    state.[0] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- VPBLENDD_256 d14 t.[1]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    d14 <- aux_1;
    leakages <- LeakAddr([4]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[4] c00
    (W8.of_int (1 %% 2^1 +
               2^1 * (1 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux_1;
    leakages <- LeakAddr([4]) :: leakages;
    aux_1 <- (d14 `^` t.[4]);
    d14 <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 0) - 96)))))]
                         ++ [2]) :: leakages;
    aux_1 <- VPSLLV_4u64 state.[2]
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 0) - 96)))));
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 0) - 96)))))]
                         ++ [2]) :: leakages;
    aux_1 <- VPSRLV_4u64 state.[2]
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 0) - 96)))));
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([3] ++ [2]) :: leakages;
    aux_1 <- (state.[2] `|` t.[3]);
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([3]) :: leakages;
    aux_1 <- (state.[3] `^` d14);
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 2) - 96)))))]
                         ++ [3]) :: leakages;
    aux_1 <- VPSLLV_4u64 state.[3]
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 2) - 96)))));
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 2) - 96)))))]
                         ++ [3]) :: leakages;
    aux_1 <- VPSRLV_4u64 state.[3]
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 2) - 96)))));
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([4] ++ [3]) :: leakages;
    aux_1 <- (state.[3] `|` t.[4]);
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([4]) :: leakages;
    aux_1 <- (state.[4] `^` d14);
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 3) - 96)))))]
                         ++ [4]) :: leakages;
    aux_1 <- VPSLLV_4u64 state.[4]
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 3) - 96)))));
    leakages <- LeakAddr([5]) :: leakages;
    t.[5] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 3) - 96)))))]
                         ++ [4]) :: leakages;
    aux_1 <- VPSRLV_4u64 state.[4]
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 3) - 96)))));
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([5] ++ [4]) :: leakages;
    aux_1 <- (state.[4] `|` t.[5]);
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([5]) :: leakages;
    aux_1 <- (state.[5] `^` d14);
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 4) - 96)))))]
                         ++ [5]) :: leakages;
    aux_1 <- VPSLLV_4u64 state.[5]
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 4) - 96)))));
    leakages <- LeakAddr([6]) :: leakages;
    t.[6] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 4) - 96)))))]
                         ++ [5]) :: leakages;
    aux_1 <- VPSRLV_4u64 state.[5]
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 4) - 96)))));
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([6] ++ [5]) :: leakages;
    aux_1 <- (state.[5] `|` t.[6]);
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([6]) :: leakages;
    aux_1 <- (state.[6] `^` d14);
    leakages <- LeakAddr([6]) :: leakages;
    state.[6] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- VPERMQ state.[2]
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux_1;
    leakages <- LeakAddr([3]) :: leakages;
    aux_1 <- VPERMQ state.[3]
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 5) - 96)))))]
                         ++ [6]) :: leakages;
    aux_1 <- VPSLLV_4u64 state.[6]
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 5) - 96)))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 5) - 96)))))]
                         ++ [6]) :: leakages;
    aux_1 <- VPSRLV_4u64 state.[6]
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 5) - 96)))));
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux_1;
    leakages <- LeakAddr([7] ++ [1]) :: leakages;
    aux_1 <- (t.[1] `|` t.[7]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- (state.[1] `^` d14);
    leakages <- LeakAddr([1]) :: leakages;
    state.[1] <- aux_1;
    leakages <- LeakAddr([4]) :: leakages;
    aux_1 <- VPERMQ state.[4]
    (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    leakages <- LeakAddr([5]) :: leakages;
    t.[5] <- aux_1;
    leakages <- LeakAddr([5]) :: leakages;
    aux_1 <- VPERMQ state.[5]
    (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
    leakages <- LeakAddr([6]) :: leakages;
    t.[6] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 1) - 96)))))]
                         ++ [1]) :: leakages;
    aux_1 <- VPSLLV_4u64 state.[1]
    (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 1) - 96)))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 1) - 96)))))]
                         ++ [1]) :: leakages;
    aux_1 <- VPSRLV_4u64 state.[1]
    (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 1) - 96)))));
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux_1;
    leakages <- LeakAddr([8] ++ [2]) :: leakages;
    aux_1 <- (t.[2] `|` t.[8]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- VPSRLDQ_256 t.[1] (W8.of_int 8);
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([7] ++ [1]) :: leakages;
    aux_1 <- ((invw t.[1]) `&` t.[7]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    leakages <- LeakAddr([6] ++ [2]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[2] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([2] ++ [4]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[4] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([4] ++ [3]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[3] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([3] ++ [2]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[2] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([4] ++ [3]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[3] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([5] ++ [8]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[8] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([2] ++ [5]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[5] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([6] ++ [7]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[7] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([5] ++ [3]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[3] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([6] ++ [8]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[8] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([6] ++ [5]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[5] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([4] ++ [7]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[7] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([8] ++ [3]) :: leakages;
    aux_1 <- ((invw state.[3]) `&` t.[8]);
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([7] ++ [5]) :: leakages;
    aux_1 <- ((invw state.[5]) `&` t.[7]);
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([2] ++ [5]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[5] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([6]) :: leakages;
    state.[6] <- aux_1;
    leakages <- LeakAddr([5] ++ [3]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[3] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux_1 <- (state.[3] `^` t.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([3] ++ [6]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[6] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([6]) :: leakages;
    state.[6] <- aux_1;
    leakages <- LeakAddr([4] ++ [8]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[8] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([5] ++ [5]) :: leakages;
    aux_1 <- (state.[5] `^` t.[5]);
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([4] ++ [6]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[6] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([6]) :: leakages;
    state.[6] <- aux_1;
    leakages <- LeakAddr([2] ++ [8]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[8] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([8] ++ [6]) :: leakages;
    aux_1 <- ((invw state.[6]) `&` t.[8]);
    leakages <- LeakAddr([6]) :: leakages;
    state.[6] <- aux_1;
    leakages <- LeakAddr([6] ++ [6]) :: leakages;
    aux_1 <- (state.[6] `^` t.[6]);
    leakages <- LeakAddr([6]) :: leakages;
    state.[6] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- VPERMQ t.[1]
    (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([0] ++ [4]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[4] state.[0]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([8]) :: leakages;
    t.[8] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- VPERMQ t.[1]
    (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
    leakages <- LeakAddr([1]) :: leakages;
    state.[1] <- aux_1;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[1] state.[0]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([1]) :: leakages;
    state.[1] <- aux_1;
    leakages <- LeakAddr([8] ++ [1]) :: leakages;
    aux_1 <- ((invw state.[1]) `&` t.[8]);
    leakages <- LeakAddr([1]) :: leakages;
    state.[1] <- aux_1;
    leakages <- LeakAddr([5] ++ [4]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[4] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([4] ++ [6]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[6] t.[4]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([6] ++ [2]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[2] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([3] ++ [7]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[7] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([3] ++ [2]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[2] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([5] ++ [7]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[7] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([7] ++ [2]) :: leakages;
    aux_1 <- ((invw state.[2]) `&` t.[7]);
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux_1 <- (state.[2] `^` t.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    state.[2] <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- VPERMQ t.[0]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux_1;
    leakages <- LeakAddr([3]) :: leakages;
    aux_1 <- VPERMQ state.[3]
    (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    leakages <- LeakAddr([3]) :: leakages;
    state.[3] <- aux_1;
    leakages <- LeakAddr([5]) :: leakages;
    aux_1 <- VPERMQ state.[5]
    (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    leakages <- LeakAddr([5]) :: leakages;
    state.[5] <- aux_1;
    leakages <- LeakAddr([6]) :: leakages;
    aux_1 <- VPERMQ state.[6]
    (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
    leakages <- LeakAddr([6]) :: leakages;
    state.[6] <- aux_1;
    leakages <- LeakAddr([3] ++ [6]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[6] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([6] ++ [5]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[5] t.[6]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (1 %% 2^1 +
                           2^1 * (1 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([5] ++ [4]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[4] t.[5]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([2] ++ [7]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[7] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (1 %% 2^1 +
                                       2^1 * (1 %% 2^1 +
                                             2^1 * (0 %% 2^1 + 2^1 * 0))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([2] ++ [4]) :: leakages;
    aux_1 <- VPBLENDD_256 state.[4] t.[2]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([3] ++ [7]) :: leakages;
    aux_1 <- VPBLENDD_256 t.[7] t.[3]
    (W8.of_int (0 %% 2^1 +
               2^1 * (0 %% 2^1 +
                     2^1 * (0 %% 2^1 +
                           2^1 * (0 %% 2^1 +
                                 2^1 * (0 %% 2^1 +
                                       2^1 * (0 %% 2^1 +
                                             2^1 * (1 %% 2^1 + 2^1 * 1))))))));
    leakages <- LeakAddr([7]) :: leakages;
    t.[7] <- aux_1;
    leakages <- LeakAddr([7] ++ [4]) :: leakages;
    aux_1 <- ((invw state.[4]) `&` t.[7]);
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux_1 <- (state.[0] `^` t.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    state.[0] <- aux_1;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux_1 <- (state.[1] `^` t.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    state.[1] <- aux_1;
    leakages <- LeakAddr([4] ++ [4]) :: leakages;
    aux_1 <- (state.[4] `^` t.[4]);
    leakages <- LeakAddr([4]) :: leakages;
    state.[4] <- aux_1;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (iotas + (W64.of_int ((32 * 0) - 0)))))]
                         ++ [0]) :: leakages;
    aux_1 <- (state.[0] `^` (loadW256 Glob.mem (W64.to_uint (iotas + (W64.of_int ((32 * 0) - 0))))));
    leakages <- LeakAddr([0]) :: leakages;
    state.[0] <- aux_1;
    aux <- (iotas + (W64.of_int 32));
    iotas <- aux;
    (aux_5, aux_4, aux_3, aux_2, aux_0) <- DEC_32 r;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
    zf <- aux_2;
    r <- aux_0;
    leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
    
    while ((! zf)) {
      leakages <- LeakAddr([2]) :: leakages;
      aux_1 <- VPSHUFD_256 state.[2]
      (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
      c00 <- aux_1;
      leakages <- LeakAddr([3] ++ [5]) :: leakages;
      aux_1 <- (state.[5] `^` state.[3]);
      c14 <- aux_1;
      leakages <- LeakAddr([6] ++ [4]) :: leakages;
      aux_1 <- (state.[4] `^` state.[6]);
      leakages <- LeakAddr([2]) :: leakages;
      t.[2] <- aux_1;
      leakages <- LeakAddr([1]) :: leakages;
      aux_1 <- (c14 `^` state.[1]);
      c14 <- aux_1;
      leakages <- LeakAddr([2]) :: leakages;
      aux_1 <- (c14 `^` t.[2]);
      c14 <- aux_1;
      aux_1 <- VPERMQ c14
      (W8.of_int (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 2))));
      leakages <- LeakAddr([4]) :: leakages;
      t.[4] <- aux_1;
      leakages <- LeakAddr([2]) :: leakages;
      aux_1 <- (c00 `^` state.[2]);
      c00 <- aux_1;
      aux_1 <- VPERMQ c00
      (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 1))));
      leakages <- LeakAddr([0]) :: leakages;
      t.[0] <- aux_1;
      aux_1 <- (c14 \vshr64u256 (W8.of_int 63));
      leakages <- LeakAddr([1]) :: leakages;
      t.[1] <- aux_1;
      aux_1 <- (c14 \vadd64u256 c14);
      leakages <- LeakAddr([2]) :: leakages;
      t.[2] <- aux_1;
      leakages <- LeakAddr([2] ++ [1]) :: leakages;
      aux_1 <- (t.[1] `|` t.[2]);
      leakages <- LeakAddr([1]) :: leakages;
      t.[1] <- aux_1;
      leakages <- LeakAddr([1]) :: leakages;
      aux_1 <- VPERMQ t.[1]
      (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      d14 <- aux_1;
      leakages <- LeakAddr([4] ++ [1]) :: leakages;
      aux_1 <- (t.[1] `^` t.[4]);
      d00 <- aux_1;
      aux_1 <- VPERMQ d00
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      d00 <- aux_1;
      leakages <- LeakAddr([0]) :: leakages;
      aux_1 <- (c00 `^` state.[0]);
      c00 <- aux_1;
      leakages <- LeakAddr([0]) :: leakages;
      aux_1 <- (c00 `^` t.[0]);
      c00 <- aux_1;
      aux_1 <- (c00 \vshr64u256 (W8.of_int 63));
      leakages <- LeakAddr([0]) :: leakages;
      t.[0] <- aux_1;
      aux_1 <- (c00 \vadd64u256 c00);
      leakages <- LeakAddr([1]) :: leakages;
      t.[1] <- aux_1;
      leakages <- LeakAddr([0] ++ [1]) :: leakages;
      aux_1 <- (t.[1] `|` t.[0]);
      leakages <- LeakAddr([1]) :: leakages;
      t.[1] <- aux_1;
      leakages <- LeakAddr([2]) :: leakages;
      aux_1 <- (state.[2] `^` d00);
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([0]) :: leakages;
      aux_1 <- (state.[0] `^` d00);
      leakages <- LeakAddr([0]) :: leakages;
      state.[0] <- aux_1;
      leakages <- LeakAddr([1]) :: leakages;
      aux_1 <- VPBLENDD_256 d14 t.[1]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      d14 <- aux_1;
      leakages <- LeakAddr([4]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[4] c00
      (W8.of_int (1 %% 2^1 +
                 2^1 * (1 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([4]) :: leakages;
      t.[4] <- aux_1;
      leakages <- LeakAddr([4]) :: leakages;
      aux_1 <- (d14 `^` t.[4]);
      d14 <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 0) - 96)))))]
                           ++ [2]) :: leakages;
      aux_1 <- VPSLLV_4u64 state.[2]
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 0) - 96)))));
      leakages <- LeakAddr([3]) :: leakages;
      t.[3] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 0) - 96)))))]
                           ++ [2]) :: leakages;
      aux_1 <- VPSRLV_4u64 state.[2]
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 0) - 96)))));
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([3] ++ [2]) :: leakages;
      aux_1 <- (state.[2] `|` t.[3]);
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([3]) :: leakages;
      aux_1 <- (state.[3] `^` d14);
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 2) - 96)))))]
                           ++ [3]) :: leakages;
      aux_1 <- VPSLLV_4u64 state.[3]
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 2) - 96)))));
      leakages <- LeakAddr([4]) :: leakages;
      t.[4] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 2) - 96)))))]
                           ++ [3]) :: leakages;
      aux_1 <- VPSRLV_4u64 state.[3]
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 2) - 96)))));
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([4] ++ [3]) :: leakages;
      aux_1 <- (state.[3] `|` t.[4]);
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([4]) :: leakages;
      aux_1 <- (state.[4] `^` d14);
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 3) - 96)))))]
                           ++ [4]) :: leakages;
      aux_1 <- VPSLLV_4u64 state.[4]
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 3) - 96)))));
      leakages <- LeakAddr([5]) :: leakages;
      t.[5] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 3) - 96)))))]
                           ++ [4]) :: leakages;
      aux_1 <- VPSRLV_4u64 state.[4]
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 3) - 96)))));
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([5] ++ [4]) :: leakages;
      aux_1 <- (state.[4] `|` t.[5]);
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([5]) :: leakages;
      aux_1 <- (state.[5] `^` d14);
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 4) - 96)))))]
                           ++ [5]) :: leakages;
      aux_1 <- VPSLLV_4u64 state.[5]
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 4) - 96)))));
      leakages <- LeakAddr([6]) :: leakages;
      t.[6] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 4) - 96)))))]
                           ++ [5]) :: leakages;
      aux_1 <- VPSRLV_4u64 state.[5]
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 4) - 96)))));
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([6] ++ [5]) :: leakages;
      aux_1 <- (state.[5] `|` t.[6]);
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([6]) :: leakages;
      aux_1 <- (state.[6] `^` d14);
      leakages <- LeakAddr([6]) :: leakages;
      state.[6] <- aux_1;
      leakages <- LeakAddr([2]) :: leakages;
      aux_1 <- VPERMQ state.[2]
      (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
      leakages <- LeakAddr([3]) :: leakages;
      t.[3] <- aux_1;
      leakages <- LeakAddr([3]) :: leakages;
      aux_1 <- VPERMQ state.[3]
      (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
      leakages <- LeakAddr([4]) :: leakages;
      t.[4] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 5) - 96)))))]
                           ++ [6]) :: leakages;
      aux_1 <- VPSLLV_4u64 state.[6]
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 5) - 96)))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 5) - 96)))))]
                           ++ [6]) :: leakages;
      aux_1 <- VPSRLV_4u64 state.[6]
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 5) - 96)))));
      leakages <- LeakAddr([1]) :: leakages;
      t.[1] <- aux_1;
      leakages <- LeakAddr([7] ++ [1]) :: leakages;
      aux_1 <- (t.[1] `|` t.[7]);
      leakages <- LeakAddr([1]) :: leakages;
      t.[1] <- aux_1;
      leakages <- LeakAddr([1]) :: leakages;
      aux_1 <- (state.[1] `^` d14);
      leakages <- LeakAddr([1]) :: leakages;
      state.[1] <- aux_1;
      leakages <- LeakAddr([4]) :: leakages;
      aux_1 <- VPERMQ state.[4]
      (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
      leakages <- LeakAddr([5]) :: leakages;
      t.[5] <- aux_1;
      leakages <- LeakAddr([5]) :: leakages;
      aux_1 <- VPERMQ state.[5]
      (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
      leakages <- LeakAddr([6]) :: leakages;
      t.[6] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_left + (W64.of_int ((32 * 1) - 96)))))]
                           ++ [1]) :: leakages;
      aux_1 <- VPSLLV_4u64 state.[1]
      (loadW256 Glob.mem (W64.to_uint (rhotates_left + (W64.of_int ((32 * 1) - 96)))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rhotates_right + (W64.of_int ((32 * 1) - 96)))))]
                           ++ [1]) :: leakages;
      aux_1 <- VPSRLV_4u64 state.[1]
      (loadW256 Glob.mem (W64.to_uint (rhotates_right + (W64.of_int ((32 * 1) - 96)))));
      leakages <- LeakAddr([2]) :: leakages;
      t.[2] <- aux_1;
      leakages <- LeakAddr([8] ++ [2]) :: leakages;
      aux_1 <- (t.[2] `|` t.[8]);
      leakages <- LeakAddr([2]) :: leakages;
      t.[2] <- aux_1;
      leakages <- LeakAddr([1]) :: leakages;
      aux_1 <- VPSRLDQ_256 t.[1] (W8.of_int 8);
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([7] ++ [1]) :: leakages;
      aux_1 <- ((invw t.[1]) `&` t.[7]);
      leakages <- LeakAddr([0]) :: leakages;
      t.[0] <- aux_1;
      leakages <- LeakAddr([6] ++ [2]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[2] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([2] ++ [4]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[4] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([4] ++ [3]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[3] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([3] ++ [2]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[2] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([4] ++ [3]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[3] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([5] ++ [8]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[8] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([2] ++ [5]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[5] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([6] ++ [7]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[7] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([5] ++ [3]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[3] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([6] ++ [8]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[8] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([6] ++ [5]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[5] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([4] ++ [7]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[7] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([8] ++ [3]) :: leakages;
      aux_1 <- ((invw state.[3]) `&` t.[8]);
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([7] ++ [5]) :: leakages;
      aux_1 <- ((invw state.[5]) `&` t.[7]);
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([2] ++ [5]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[5] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([6]) :: leakages;
      state.[6] <- aux_1;
      leakages <- LeakAddr([5] ++ [3]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[3] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([3] ++ [3]) :: leakages;
      aux_1 <- (state.[3] `^` t.[3]);
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([3] ++ [6]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[6] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([6]) :: leakages;
      state.[6] <- aux_1;
      leakages <- LeakAddr([4] ++ [8]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[8] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([5] ++ [5]) :: leakages;
      aux_1 <- (state.[5] `^` t.[5]);
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([4] ++ [6]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[6] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([6]) :: leakages;
      state.[6] <- aux_1;
      leakages <- LeakAddr([2] ++ [8]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[8] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([8] ++ [6]) :: leakages;
      aux_1 <- ((invw state.[6]) `&` t.[8]);
      leakages <- LeakAddr([6]) :: leakages;
      state.[6] <- aux_1;
      leakages <- LeakAddr([6] ++ [6]) :: leakages;
      aux_1 <- (state.[6] `^` t.[6]);
      leakages <- LeakAddr([6]) :: leakages;
      state.[6] <- aux_1;
      leakages <- LeakAddr([1]) :: leakages;
      aux_1 <- VPERMQ t.[1]
      (W8.of_int (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([0] ++ [4]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[4] state.[0]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([8]) :: leakages;
      t.[8] <- aux_1;
      leakages <- LeakAddr([1]) :: leakages;
      aux_1 <- VPERMQ t.[1]
      (W8.of_int (1 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 0))));
      leakages <- LeakAddr([1]) :: leakages;
      state.[1] <- aux_1;
      leakages <- LeakAddr([0] ++ [1]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[1] state.[0]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([1]) :: leakages;
      state.[1] <- aux_1;
      leakages <- LeakAddr([8] ++ [1]) :: leakages;
      aux_1 <- ((invw state.[1]) `&` t.[8]);
      leakages <- LeakAddr([1]) :: leakages;
      state.[1] <- aux_1;
      leakages <- LeakAddr([5] ++ [4]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[4] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([4] ++ [6]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[6] t.[4]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([6] ++ [2]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[2] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([3] ++ [7]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[7] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([3] ++ [2]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[2] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([5] ++ [7]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[7] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([7] ++ [2]) :: leakages;
      aux_1 <- ((invw state.[2]) `&` t.[7]);
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([2] ++ [2]) :: leakages;
      aux_1 <- (state.[2] `^` t.[2]);
      leakages <- LeakAddr([2]) :: leakages;
      state.[2] <- aux_1;
      leakages <- LeakAddr([0]) :: leakages;
      aux_1 <- VPERMQ t.[0]
      (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 0))));
      leakages <- LeakAddr([0]) :: leakages;
      t.[0] <- aux_1;
      leakages <- LeakAddr([3]) :: leakages;
      aux_1 <- VPERMQ state.[3]
      (W8.of_int (3 %% 2^2 + 2^2 * (2 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
      leakages <- LeakAddr([3]) :: leakages;
      state.[3] <- aux_1;
      leakages <- LeakAddr([5]) :: leakages;
      aux_1 <- VPERMQ state.[5]
      (W8.of_int (1 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
      leakages <- LeakAddr([5]) :: leakages;
      state.[5] <- aux_1;
      leakages <- LeakAddr([6]) :: leakages;
      aux_1 <- VPERMQ state.[6]
      (W8.of_int (2 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 1))));
      leakages <- LeakAddr([6]) :: leakages;
      state.[6] <- aux_1;
      leakages <- LeakAddr([3] ++ [6]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[6] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([6] ++ [5]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[5] t.[6]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (1 %% 2^1 +
                             2^1 * (1 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([5] ++ [4]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[4] t.[5]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([2] ++ [7]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[7] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (1 %% 2^1 +
                                         2^1 * (1 %% 2^1 +
                                               2^1 * (0 %% 2^1 + 2^1 * 0))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([2] ++ [4]) :: leakages;
      aux_1 <- VPBLENDD_256 state.[4] t.[2]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([3] ++ [7]) :: leakages;
      aux_1 <- VPBLENDD_256 t.[7] t.[3]
      (W8.of_int (0 %% 2^1 +
                 2^1 * (0 %% 2^1 +
                       2^1 * (0 %% 2^1 +
                             2^1 * (0 %% 2^1 +
                                   2^1 * (0 %% 2^1 +
                                         2^1 * (0 %% 2^1 +
                                               2^1 * (1 %% 2^1 + 2^1 * 1))))))));
      leakages <- LeakAddr([7]) :: leakages;
      t.[7] <- aux_1;
      leakages <- LeakAddr([7] ++ [4]) :: leakages;
      aux_1 <- ((invw state.[4]) `&` t.[7]);
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([0] ++ [0]) :: leakages;
      aux_1 <- (state.[0] `^` t.[0]);
      leakages <- LeakAddr([0]) :: leakages;
      state.[0] <- aux_1;
      leakages <- LeakAddr([1] ++ [1]) :: leakages;
      aux_1 <- (state.[1] `^` t.[1]);
      leakages <- LeakAddr([1]) :: leakages;
      state.[1] <- aux_1;
      leakages <- LeakAddr([4] ++ [4]) :: leakages;
      aux_1 <- (state.[4] `^` t.[4]);
      leakages <- LeakAddr([4]) :: leakages;
      state.[4] <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (iotas + (W64.of_int ((32 * 0) - 0)))))]
                           ++ [0]) :: leakages;
      aux_1 <- (state.[0] `^` (loadW256 Glob.mem (W64.to_uint (iotas + (W64.of_int ((32 * 0) - 0))))));
      leakages <- LeakAddr([0]) :: leakages;
      state.[0] <- aux_1;
      aux <- (iotas + (W64.of_int 32));
      iotas <- aux;
      (aux_5, aux_4, aux_3, aux_2, aux_0) <- DEC_32 r;
       _0 <- aux_5;
       _1 <- aux_4;
       _2 <- aux_3;
      zf <- aux_2;
      r <- aux_0;
    leakages <- LeakCond((! zf)) :: LeakAddr([]) :: leakages;
    
    }
    return (state);
  }
  
  proc keccak_init () : W256.t Array7.t = {
    var aux_0: int;
    var aux: W256.t;
    
    var state:W256.t Array7.t;
    var i:int;
    state <- witness;
    aux <- VPBROADCAST_4u64 g_zero;
    leakages <- LeakAddr([0]) :: leakages;
    state.[0] <- aux;
    leakages <- LeakFor(1,7) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 7) {
      leakages <- LeakAddr([0]) :: leakages;
      aux <- state.[0];
      leakages <- LeakAddr([i]) :: leakages;
      state.[i] <- aux;
      i <- i + 1;
    }
    return (state);
  }
  
  proc init_s_state () : W64.t Array28.t = {
    var aux_0: int;
    var aux: W256.t;
    
    var s_state:W64.t Array28.t;
    var zero:W256.t;
    var i:int;
    s_state <- witness;
    aux <- VPBROADCAST_4u64 g_zero;
    zero <- aux;
    leakages <- LeakFor(0,7) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 7) {
      aux <- zero;
      leakages <- LeakAddr([i]) :: leakages;
      s_state <-
      Array28.init
      (WArray224.get64 (WArray224.set256 (WArray224.init64 (fun i => s_state.[i])) i aux));
      i <- i + 1;
    }
    return (s_state);
  }
  
  proc add_full_block (state:W256.t Array7.t, s_state:W64.t Array28.t,
                       a_jagged:W64.t, in_0:W64.t, inlen:W64.t, rate:W64.t) : 
  W256.t Array7.t * W64.t Array28.t * W64.t * W64.t = {
    var aux_0: int;
    var aux: W64.t;
    var aux_1: W256.t;
    
    var rate8:W64.t;
    var j:W64.t;
    var t:W64.t;
    var l:W64.t;
    var i:int;
    
    aux <- rate;
    rate8 <- aux;
    aux <- (rate8 `>>` (W8.of_int 3));
    rate8 <- aux;
    aux <- (W64.of_int 0);
    j <- aux;
    
    leakages <- LeakCond((j \ult rate8)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult rate8)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + ((W64.of_int 8) * j))))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * j))));
      t <- aux;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (a_jagged + ((W64.of_int 8) * j))))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (a_jagged + ((W64.of_int 8) * j))));
      l <- aux;
      aux <- t;
      leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
      s_state.[(W64.to_uint l)] <- aux;
      aux <- (j + (W64.of_int 1));
      j <- aux;
    leakages <- LeakCond((j \ult rate8)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s_state.[0];
    t <- aux;
    aux <- t;
    leakages <- LeakAddr([1]) :: leakages;
    s_state.[1] <- aux;
    aux <- t;
    leakages <- LeakAddr([2]) :: leakages;
    s_state.[2] <- aux;
    aux <- t;
    leakages <- LeakAddr([3]) :: leakages;
    s_state.[3] <- aux;
    leakages <- LeakFor(0,7) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 7) {
      leakages <- LeakAddr([i] ++ [i]) :: leakages;
      aux_1 <- (state.[i] `^` (get256
                              (WArray224.init64 (fun i => s_state.[i])) i));
      leakages <- LeakAddr([i]) :: leakages;
      state.[i] <- aux_1;
      i <- i + 1;
    }
    aux <- (in_0 + rate);
    in_0 <- aux;
    aux <- (inlen - rate);
    inlen <- aux;
    return (state, s_state, in_0, inlen);
  }
  
  proc add_final_block (state:W256.t Array7.t, s_state:W64.t Array28.t,
                        a_jagged:W64.t, in_0:W64.t, inlen:W64.t,
                        trail_byte:W8.t, rate:W64.t) : W256.t Array7.t = {
    var aux_2: int;
    var aux_1: W8.t;
    var aux_0: W64.t;
    var aux_3: W256.t;
    var aux: W64.t Array28.t;
    
    var inlen8:W64.t;
    var j:W64.t;
    var t:W64.t;
    var l:W64.t;
    var c:W8.t;
    var i:int;
    
    aux <@ init_s_state ();
    s_state <- aux;
    aux_0 <- inlen;
    inlen8 <- aux_0;
    aux_0 <- (inlen8 `>>` (W8.of_int 3));
    inlen8 <- aux_0;
    aux_0 <- (W64.of_int 0);
    j <- aux_0;
    
    leakages <- LeakCond((j \ult inlen8)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult inlen8)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + ((W64.of_int 8) * j))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * j))));
      t <- aux_0;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (a_jagged + ((W64.of_int 8) * j))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (a_jagged + ((W64.of_int 8) * j))));
      l <- aux_0;
      aux_0 <- t;
      leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
      s_state.[(W64.to_uint l)] <- aux_0;
      aux_0 <- (j + (W64.of_int 1));
      j <- aux_0;
    leakages <- LeakCond((j \ult inlen8)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (a_jagged + ((W64.of_int 8) * j))))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (a_jagged + ((W64.of_int 8) * j))));
    l <- aux_0;
    aux_0 <- (l `<<` (W8.of_int 3));
    l <- aux_0;
    aux_0 <- (j `<<` (W8.of_int 3));
    j <- aux_0;
    
    leakages <- LeakCond((j \ult inlen)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult inlen)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + j)))]) :: leakages;
      aux_1 <- (loadW8 Glob.mem (W64.to_uint (in_0 + j)));
      c <- aux_1;
      aux_1 <- c;
      leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
      s_state <-
      Array28.init
      (WArray224.get64 (WArray224.set8 (WArray224.init64 (fun i => s_state.[i])) (W64.to_uint l) aux_1));
      aux_0 <- (j + (W64.of_int 1));
      j <- aux_0;
      aux_0 <- (l + (W64.of_int 1));
      l <- aux_0;
    leakages <- LeakCond((j \ult inlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux_1 <- trail_byte;
    leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
    s_state <-
    Array28.init
    (WArray224.get64 (WArray224.set8 (WArray224.init64 (fun i => s_state.[i])) (W64.to_uint l) aux_1));
    aux_0 <- rate;
    j <- aux_0;
    aux_0 <- (j - (W64.of_int 1));
    j <- aux_0;
    aux_0 <- (j `>>` (W8.of_int 3));
    j <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (a_jagged + ((W64.of_int 8) * j))))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (a_jagged + ((W64.of_int 8) * j))));
    l <- aux_0;
    aux_0 <- (l `<<` (W8.of_int 3));
    l <- aux_0;
    aux_0 <- rate;
    j <- aux_0;
    aux_0 <- (j - (W64.of_int 1));
    j <- aux_0;
    aux_0 <- (j `&` (W64.of_int 7));
    j <- aux_0;
    aux_0 <- (l + j);
    l <- aux_0;
    leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
    aux_1 <- ((get8 (WArray224.init64 (fun i => s_state.[i]))
              (W64.to_uint l)) `^` (W8.of_int 128));
    leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
    s_state <-
    Array28.init
    (WArray224.get64 (WArray224.set8 (WArray224.init64 (fun i => s_state.[i])) (W64.to_uint l) aux_1));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- s_state.[0];
    t <- aux_0;
    aux_0 <- t;
    leakages <- LeakAddr([1]) :: leakages;
    s_state.[1] <- aux_0;
    aux_0 <- t;
    leakages <- LeakAddr([2]) :: leakages;
    s_state.[2] <- aux_0;
    aux_0 <- t;
    leakages <- LeakAddr([3]) :: leakages;
    s_state.[3] <- aux_0;
    leakages <- LeakFor(0,7) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 7) {
      leakages <- LeakAddr([i] ++ [i]) :: leakages;
      aux_3 <- (state.[i] `^` (get256
                              (WArray224.init64 (fun i => s_state.[i])) i));
      leakages <- LeakAddr([i]) :: leakages;
      state.[i] <- aux_3;
      i <- i + 1;
    }
    return (state);
  }
  
  proc xtr_full_block (state:W256.t Array7.t, a_jagged:W64.t, out:W64.t,
                       len:W64.t) : W64.t = {
    var aux: int;
    var aux_1: W64.t;
    var aux_0: W256.t;
    
    var i:int;
    var s_state:W64.t Array28.t;
    var len8:W64.t;
    var j:W64.t;
    var l:W64.t;
    var t:W64.t;
    s_state <- witness;
    leakages <- LeakFor(0,7) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 7) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- state.[i];
      leakages <- LeakAddr([i]) :: leakages;
      s_state <-
      Array28.init
      (WArray224.get64 (WArray224.set256 (WArray224.init64 (fun i => s_state.[i])) i aux_0));
      i <- i + 1;
    }
    aux_1 <- len;
    len8 <- aux_1;
    aux_1 <- (len8 `>>` (W8.of_int 3));
    len8 <- aux_1;
    aux_1 <- (W64.of_int 0);
    j <- aux_1;
    
    leakages <- LeakCond((j \ult len8)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult len8)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (a_jagged + ((W64.of_int 8) * j))))]) :: leakages;
      aux_1 <- (loadW64 Glob.mem (W64.to_uint (a_jagged + ((W64.of_int 8) * j))));
      l <- aux_1;
      leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
      aux_1 <- s_state.[(W64.to_uint l)];
      t <- aux_1;
      aux_1 <- t;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + ((W64.of_int 8) * j))))]) :: leakages;
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + ((W64.of_int 8) * j))) aux_1;
      aux_1 <- (j + (W64.of_int 1));
      j <- aux_1;
    leakages <- LeakCond((j \ult len8)) :: LeakAddr([]) :: leakages;
    
    }
    aux_1 <- (out + len);
    out <- aux_1;
    return (out);
  }
  
  proc xtr_bytes (state:W256.t Array7.t, a_jagged:W64.t, out:W64.t, len:W64.t) : 
  W64.t = {
    var aux: int;
    var aux_2: W8.t;
    var aux_1: W64.t;
    var aux_0: W256.t;
    
    var i:int;
    var s_state:W64.t Array28.t;
    var len8:W64.t;
    var j:W64.t;
    var l:W64.t;
    var t:W64.t;
    var c:W8.t;
    s_state <- witness;
    leakages <- LeakFor(0,7) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 7) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- state.[i];
      leakages <- LeakAddr([i]) :: leakages;
      s_state <-
      Array28.init
      (WArray224.get64 (WArray224.set256 (WArray224.init64 (fun i => s_state.[i])) i aux_0));
      i <- i + 1;
    }
    aux_1 <- len;
    len8 <- aux_1;
    aux_1 <- (len8 `>>` (W8.of_int 3));
    len8 <- aux_1;
    aux_1 <- (W64.of_int 0);
    j <- aux_1;
    
    leakages <- LeakCond((j \ult len8)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult len8)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (a_jagged + ((W64.of_int 8) * j))))]) :: leakages;
      aux_1 <- (loadW64 Glob.mem (W64.to_uint (a_jagged + ((W64.of_int 8) * j))));
      l <- aux_1;
      leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
      aux_1 <- s_state.[(W64.to_uint l)];
      t <- aux_1;
      aux_1 <- t;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + ((W64.of_int 8) * j))))]) :: leakages;
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + ((W64.of_int 8) * j))) aux_1;
      aux_1 <- (j + (W64.of_int 1));
      j <- aux_1;
    leakages <- LeakCond((j \ult len8)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (a_jagged + ((W64.of_int 8) * j))))]) :: leakages;
    aux_1 <- (loadW64 Glob.mem (W64.to_uint (a_jagged + ((W64.of_int 8) * j))));
    l <- aux_1;
    aux_1 <- (j `<<` (W8.of_int 3));
    j <- aux_1;
    aux_1 <- (l `<<` (W8.of_int 3));
    l <- aux_1;
    
    leakages <- LeakCond((j \ult len)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult len)) {
      leakages <- LeakAddr([(W64.to_uint l)]) :: leakages;
      aux_2 <- (get8 (WArray224.init64 (fun i => s_state.[i]))
               (W64.to_uint l));
      c <- aux_2;
      aux_2 <- c;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + j)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + j)) aux_2;
      aux_1 <- (j + (W64.of_int 1));
      j <- aux_1;
      aux_1 <- (l + (W64.of_int 1));
      l <- aux_1;
    leakages <- LeakCond((j \ult len)) :: LeakAddr([]) :: leakages;
    
    }
    aux_1 <- (out + len);
    out <- aux_1;
    return (out);
  }
  
  proc absorb (state:W256.t Array7.t, rhotates_left:W64.t,
               rhotates_right:W64.t, iotas:W64.t, a_jagged:W64.t, in_0:W64.t,
               inlen:W64.t, trail_byte:W8.t, rate:W64.t) : W256.t Array7.t = {
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux: W64.t Array28.t;
    var aux_0: W256.t Array7.t;
    
    var s_state:W64.t Array28.t;
    s_state <- witness;
    aux <@ init_s_state ();
    s_state <- aux;
    
    leakages <- LeakCond((rate \ule inlen)) :: LeakAddr([]) :: leakages;
    
    while ((rate \ule inlen)) {
      (aux_0, aux, aux_2, aux_1) <@ add_full_block (state, s_state, a_jagged,
      in_0, inlen, rate);
      state <- aux_0;
      s_state <- aux;
      in_0 <- aux_2;
      inlen <- aux_1;
      aux_0 <@ __keccakf1600_avx2 (state, rhotates_left, rhotates_right,
      iotas);
      state <- aux_0;
    leakages <- LeakCond((rate \ule inlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux_0 <@ add_final_block (state, s_state, a_jagged, in_0, inlen,
    trail_byte, rate);
    state <- aux_0;
    return (state);
  }
  
  proc squeeze (state:W256.t Array7.t, rhotates_left:W64.t,
                rhotates_right:W64.t, iotas:W64.t, a_jagged:W64.t, out:W64.t,
                outlen:W64.t, rate:W64.t) : unit = {
    var aux_0: W64.t;
    var aux: W256.t Array7.t;
    
    
    
    
    leakages <- LeakCond((rate \ult outlen)) :: LeakAddr([]) :: leakages;
    
    while ((rate \ult outlen)) {
      aux <@ __keccakf1600_avx2 (state, rhotates_left, rhotates_right,
      iotas);
      state <- aux;
      aux_0 <@ xtr_full_block (state, a_jagged, out, rate);
      out <- aux_0;
      aux_0 <- (outlen - rate);
      outlen <- aux_0;
    leakages <- LeakCond((rate \ult outlen)) :: LeakAddr([]) :: leakages;
    
    }
    aux <@ __keccakf1600_avx2 (state, rhotates_left, rhotates_right, iotas);
    state <- aux;
    aux_0 <@ xtr_bytes (state, a_jagged, out, outlen);
    out <- aux_0;
    return ();
  }
  
  proc __keccak1600_avx2 (out:W64.t, outlen:W64.t, rhotates_left:W64.t,
                          rhotates_right:W64.t, iotas:W64.t, a_jagged:W64.t,
                          in_0:W64.t, inlen:W64.t, trail_byte:W8.t,
                          rate:W64.t) : unit = {
    var aux: W256.t Array7.t;
    
    var state:W256.t Array7.t;
    state <- witness;
    aux <@ keccak_init ();
    state <- aux;
    aux <@ absorb (state, rhotates_left, rhotates_right, iotas, a_jagged,
    in_0, inlen, trail_byte, rate);
    state <- aux;
    squeeze (state, rhotates_left, rhotates_right, iotas, a_jagged, out,
    outlen, rate);
    return ();
  }
  
  proc keccak1600_avx2 (out:W64.t, outlen:W64.t, in_0:W64.t, inlen:W64.t,
                        config:W64.t, glob_0:W64.t) : unit = {
    var aux: W8.t;
    var aux_0: W64.t;
    
    var trail_byte:W8.t;
    var rate:W64.t;
    var rhotates_left:W64.t;
    var rhotates_right:W64.t;
    var iotas:W64.t;
    var a_jagged:W64.t;
    
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (config + (W64.of_int (8 * 0)))))]) :: leakages;
    aux <- (loadW8 Glob.mem (W64.to_uint (config + (W64.of_int (8 * 0)))));
    trail_byte <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (config + (W64.of_int (8 * 1)))))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (config + (W64.of_int (8 * 1)))));
    rate <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (glob_0 + (W64.of_int (8 * 0)))))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (glob_0 + (W64.of_int (8 * 0)))));
    rhotates_left <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (glob_0 + (W64.of_int (8 * 1)))))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (glob_0 + (W64.of_int (8 * 1)))));
    rhotates_right <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (glob_0 + (W64.of_int (8 * 2)))))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (glob_0 + (W64.of_int (8 * 2)))));
    iotas <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (glob_0 + (W64.of_int (8 * 3)))))]) :: leakages;
    aux_0 <- (loadW64 Glob.mem (W64.to_uint (glob_0 + (W64.of_int (8 * 3)))));
    a_jagged <- aux_0;
    __keccak1600_avx2 (out, outlen, rhotates_left, rhotates_right, iotas,
    a_jagged, in_0, inlen, trail_byte, rate);
    return ();
  }
}.
end T.

