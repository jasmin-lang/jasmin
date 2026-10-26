require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.

(* ----------------------------------------------------------------------------*)
require Test_arr_sum Test_arr_sum_specs.
require import BArray5.

lemma test_arr_sum_safe _x _b_x : Test_arr_sum_specs.test_spec _x _b_x.
proof.
  rewrite /Test_arr_sum_specs.test_spec; proc; wp.
  while (0 <= i /\ b_sum /\ BArray5.is_init b_x 0 5).
  + by auto => /> &m; rewrite /BArray5.is_init /BArray5.is_init_cell /#.
  by auto.
qed.

(* ----------------------------------------------------------------------------*)
require Test_array.
require import BArray8.

lemma test_array_safe :
  hoare [ Test_array.M.test : true ==> true | Test_array.Assertion_failure => false ].
proof. by proc; auto. qed.

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
  split; 1: by rewrite /BArray32.is_init /#.
  move=> b_a i h4 h0 h4' hinit; have ->> : i = 4 by smt().
  move=> k hk1 hk2; rewrite SBArray32_16.is_init_cell_get 1,2:/#.
  by move: hinit; rewrite /BArray32.is_init /#.
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
require Test_init_arr_sum Test_init_arr_sum_specs.
require import BArray10.

lemma test_init_arr_sum_safe _x _b_x _y _b_y _z _b_z :
  Test_init_arr_sum_specs.test_spec _x _b_x _y _b_y _z _b_z.
proof.
  rewrite /Test_init_arr_sum_specs.test_spec; proc; wp.
  while (0 <= i <= 5 /\ b_i = (0 < i) /\ BArray10.is_init b_x 0 10 /\
         BArray10.is_init b_y 0 10 /\ BArray10.is_init b_z 0 (2 * i)).
  + by auto => /> &m; rewrite /BArray10.is_init /#.
  by auto => /> /#.
qed.

(* ----------------------------------------------------------------------------*)
require Test_init_pos_func Test_init_pos_func_specs.
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

(* the specification of [init_pos], weaker *)
lemma init_pos_spec_safe _x _b_x _i : Test_init_pos_func_specs.init_pos_spec _x _b_x _i.
proof.
  rewrite /Test_init_pos_func_specs.init_pos_spec.
  conseq (init_pos_safe _b_x _i) => /> &m *.
  by rewrite /BArray5.is_init /#.
qed.

lemma test2_safe _x _b_x : Test_init_pos_func_specs.test2_spec _x _b_x.
proof.
  rewrite /Test_init_pos_func_specs.test2_spec; proc; auto.
  ecall (init_pos_safe b_x0 ix); auto => /> hx r h.
  move: hx; rewrite /BArray5.is_init; smt().
qed.

lemma test_safe _x _b_x : Test_init_pos_func_specs.test_spec _x _b_x.
proof.
  rewrite /Test_init_pos_func_specs.test_spec; proc; auto.
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

(* ----------------------------------------------------------------------------*)
require Test_call_post Test_call_post_specs.
require import BArray16.

lemma fill_safe _x _b_x : Test_call_post_specs.fill_spec _x _b_x.
proof.
  rewrite /Test_call_post_specs.fill_spec; proc; wp.
  while (0 <= i <= 4 /\ BArray16.is_init b_x 0 (4 * i)).
  + auto => /> &m h0 _ hinit h4; split; 1: smt().
    move=> _ _; split; 1: smt().
    rewrite /BArray16.is_init => k hk1 hk2 /=.
    move: hinit; rewrite /BArray16.is_init /#.
  auto => />; split; 1: by rewrite /BArray16.is_init /#.
  by move=> b i h4 h0 h4' hinit; have <- : 4 * i = 16 by smt().
qed.

(* [sum] reads the array returned by [fill]: the specification of [fill]
   states that it is initialised. *)
lemma sum_safe :
  hoare [ Test_call_post.M.sum : true ==> true | Test_call_post.Assertion_failure => false ].
proof.
  proc; wp.
  while (0 <= i /\ b_s /\ BArray16.is_init b_a 0 16).
  + by auto => /> &m; rewrite /BArray16.is_init /#.
  wp; ecall (fill_safe x b_x); auto => /> /#.
qed.

(* ----------------------------------------------------------------------------*)
require Test_full_pre Test_full_pre_specs.
require import BArray32.

(* The precondition gives the initialisation of [x]: the body tests only the
   bounds of the accesses in the loop. *)
lemma sum_full_pre_safe _x _b_x : Test_full_pre_specs.sum_spec _x _b_x.
proof.
  rewrite /Test_full_pre_specs.sum_spec; proc; wp.
  while (1 <= i <= 3); 1: by auto => /#.
  by auto.
qed.
