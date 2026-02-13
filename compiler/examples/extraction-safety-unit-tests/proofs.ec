
require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JWord Jcheck JSafety.

(* ----------------------------------------------------------------------------*)
require Test_arr_sum.

lemma Test_arr_sum_ok _x _b_x : Test_arr_sum.test_spec _x _b_x.
proof.
  rewrite /Test_arr_sum.test_spec .
  proc; auto .
  while ((valid trace_test) /\ (0 <= i)).
  + auto => &m.
    rewrite /valid all_cat => /> _ /#.
  auto.
qed.

(* ----------------------------------------------------------------------------*)
require Test_array.

lemma Test_array_ok : Test_array.test_spec.
proof.
  rewrite /Test_array.test_spec.
  proc; auto.
qed.

(* ----------------------------------------------------------------------------*)
require Test_glob_array.

lemma Test_glob_array_ok : Test_glob_array.get_global_spec.
proof.
  rewrite /get_global_spec.
  proc; auto.
qed.

(* ----------------------------------------------------------------------------*)
require Test_glob_var.

lemma Test_glob_var_ok : Test_glob_var.zero_spec.
proof.
  rewrite /Test_glob_var.zero_spec .
  proc; auto.
qed.

(* ----------------------------------------------------------------------------*)
require Test_init_arr_sum.

lemma Test_init_arr_sum_ok _x _b_x _y _b_y _z _b_z :
       Test_init_arr_sum.test_spec _x _b_x _y _b_y _z _b_z.
proof.
  rewrite /test_spec.
  proc; auto.
  while ((valid trace_test) /\ 0 <= i /\ BArray10.is_init b_z 0 (2 * i)).
  + auto => &m.
    rewrite /is_init /valid !all_cat => /> /#.
  auto => &m.
  rewrite /is_init /valid !all_cat => /> /#.
qed.

(* ----------------------------------------------------------------------------*)
require Test_init_pos_func.

lemma init_pos_proof _x _b_x _i : Test_init_pos_func.init_pos_spec _x _b_x _i.
proof.
  rewrite /Test_init_pos_func.init_pos_spec.
  proc; auto.
  move=> &hr.
  rewrite !and_iota /= /is_init /valid /= /#.
qed .

lemma test2_proof _x _b_x : Test_init_pos_func.test2_spec _x _b_x.
proof.
  rewrite /Test_init_pos_func.test2_spec.
  proc; auto.
  have init_pos_proof_aux := init_pos_proof; rewrite /Test_init_pos_func.init_pos_spec in init_pos_proof_aux;
  ecall (init_pos_proof_aux param_0 (BArray5.init_arr (W8.of_int 255)) param).
  auto => &hr.
  rewrite and_iota /is_init /valid /= => /> ? result.
  rewrite and_iota /= all_cat /= => />.
  by move => ->.
qed .

lemma test_proof _x _b_x : Test_init_pos_func.test_spec _x _b_x.
proof.
  rewrite /test_spec.
  proc; auto.
  while ((valid trace_test) /\  (((0 <= i) /\ (i <= 5)) /\
                                (BArray5.is_init b_x 0 i))).
  + auto.
    have init_pos_proof_aux := init_pos_proof; rewrite /init_pos_spec in init_pos_proof_aux;
     ecall (init_pos_proof_aux param_0 b_param param).
    auto.
    rewrite /is_init /valid /= => /> &hr 5? result.
    rewrite !and_iota /= !all_cat /= => 2?.
    smt().
  auto => &m.
  rewrite /is_init /valid => />; split; first smt().
  move => *; rewrite all_cat /= /#.
qed .

(* ----------------------------------------------------------------------------*)
require Test_mem.

lemma Test_mem_ok _str : Test_mem.test_spec _str.
proof.
rewrite /test_spec.
proc; auto => &m /> *.
smt (all_cat).
qed.
