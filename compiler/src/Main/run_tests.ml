open OUnit

let () =
  let suite1 = "IL" >::: Tests_IL.tests in
  let suite2 = "IL" >::: Tests_Arith.tests_U64 in
  ignore (run_test_tt_main suite1);
  ignore (run_test_tt_main suite2)
