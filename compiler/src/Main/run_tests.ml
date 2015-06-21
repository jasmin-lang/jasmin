open OUnit

let () =
  let suite = "IL" >::: Tests_IL.tests in
  ignore (run_test_tt_main suite)
