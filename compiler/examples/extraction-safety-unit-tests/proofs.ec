require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.

(* ----------------------------------------------------------------------------*)
require Test_arr_sum.
require import BArray5.

lemma test_arr_sum_safe :
  hoare [ Test_arr_sum.M.test :
          BArray5.is_init b_x 0 5 ==> true | Test_arr_sum.Assertion_failure => false ].
proof.
  proc; wp.
  while (0 <= i /\ b_sum /\ BArray5.is_init b_x 0 5).
  + by auto => /> &m; rewrite /BArray5.is_init /BArray5.is_init_cell /#.
  by auto.
qed.

(* ----------------------------------------------------------------------------*)
require Test_array.
require import BArray8.

lemma test_array_safe :
  hoare [ Test_array.M.test : true ==> true | Test_array.Assertion_failure => false ].
proof.
  proc; auto => /> i *.
  by rewrite /BArray8.is_init_cell /BArray8.fill8 initiE /#.
qed.

(* ----------------------------------------------------------------------------*)
require Test_cast.

lemma test_cast_safe :
  hoare [ Test_cast.M.test : true ==> true | Test_cast.Assertion_failure => false ].
proof. by proc; auto. qed.

(* ----------------------------------------------------------------------------*)
require Test_copy_sub.
require import BArray16 BArray32 SBArray32_16.

(* The copied sub-array [a[1:2]] is initialised: the loop initialises [a]. *)
lemma test_copy_sub_safe :
  hoare [ Test_copy_sub.M.test : true ==> true | Test_copy_sub.Assertion_failure => false ].
proof.
  proc; wp.
  while (0 <= i <= 4 /\ BArray32.is_init b_a 0 (8 * i)).
  + auto => /> &m h0 _ hinit h4; split; 1: smt().
    move=> _ _; split; 1: smt().
    move: hinit; rewrite /BArray32.is_init => hinit k hk1 hk2 /=; smt().
  auto => />.
  split; 1: by rewrite /BArray16.is_init /#.
  move=> b_a i h4 h0 h4' hinit; have ->> : i = 4 by smt().
  have hb : forall k, 0 <= k < 16 =>
    BArray16.is_init_cell (BArray16.fill8 0 16 (W8.of_int 255)) k.
  + by move=> k hk; rewrite /BArray16.is_init_cell /BArray16.fill8 BArray16.initiE /#.
  split.
  + move=> k hk1 hk2; rewrite SBArray32_16.is_init_cell_get 1,2:/#.
    by move: hinit; rewrite /BArray32.is_init /#.
  by move=> _; split => [k * | _ k *]; apply hb => /#.
qed.

(* ----------------------------------------------------------------------------*)
require Test_glob_array.

lemma test_glob_array_safe :
  hoare [ Test_glob_array.M.get_global :
          true ==> true | Test_glob_array.Assertion_failure => false ].
proof. by proc; auto. qed.

(* ----------------------------------------------------------------------------*)
require Test_glob_var.

lemma test_glob_var_safe :
  hoare [ Test_glob_var.M.zero : true ==> true | Test_glob_var.Assertion_failure => false ].
proof. by proc; auto. qed.

(* ----------------------------------------------------------------------------*)
require Test_init_arr_sum.
require import BArray10.

lemma test_init_arr_sum_safe :
  hoare [ Test_init_arr_sum.M.test :
          BArray10.is_init b_x 0 10 /\ BArray10.is_init b_y 0 10 ==>
          BArray10.is_init res.`2 0 10 | Test_init_arr_sum.Assertion_failure => false ].
proof.
  proc; wp.
  while (0 <= i <= 5 /\ b_i = (0 < i) /\ BArray10.is_init b_x 0 10 /\
         BArray10.is_init b_y 0 10 /\ BArray10.is_init b_z 0 (2 * i)).
  + by auto => /> &m; rewrite /BArray10.is_init /#.
  by auto => /> /#.
qed.

(* ----------------------------------------------------------------------------*)
require Test_init_pos_func.
require import BArray5.

(* [init_pos] initialises the cell [i] and leaves the others as they were *)
lemma init_pos_safe (bx : BArray5.t) (i0 : int) :
  hoare [ Test_init_pos_func.M.init_pos :
          0 <= i < 5 /\ b_x = bx /\ i = i0 ==>
          forall k, BArray5.is_init_cell res.`2 k = (k = i0 \/ BArray5.is_init_cell bx k)
          | Test_init_pos_func.Assertion_failure => false ].
proof.
  proc; auto => /> *.
  by rewrite /BArray5.is_init_cell; smt(get_setE).
qed.

lemma test2_safe :
  hoare [ Test_init_pos_func.M.test2 :
          BArray5.is_init b_x 0 5 ==> true | Test_init_pos_func.Assertion_failure => false ].
proof.
  proc; auto.
  ecall (init_pos_safe b_x0 ix); auto => /> &m hx r h.
  move: hx; rewrite /BArray5.is_init; smt().
qed.

lemma test_safe :
  hoare [ Test_init_pos_func.M.test :
          true ==> BArray5.is_init res.`2 0 5 | Test_init_pos_func.Assertion_failure => false ].
proof.
  proc; auto.
  while (0 <= i <= 5 /\ b_i /\ BArray5.is_init b_x 0 i).
  + wp; ecall (init_pos_safe b_x0 ix); auto => /> &m h0 _ hx h5 r h.
    move: hx; rewrite /BArray5.is_init; smt().
  by auto => /> /#.
qed.

(* ----------------------------------------------------------------------------*)
require Test_mem.

lemma test_mem_safe :
  hoare [ Test_mem.M.test :
          0 <= str /\ str + 8 < W64.modulus /\ is_valid W64.modulus Glob.mem_v str 8 ==>
          true | Test_mem.Assertion_failure => false ].
proof. by proc; auto => /> &m /#. qed.
