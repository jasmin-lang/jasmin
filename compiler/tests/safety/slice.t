  $ ../../jasmin-checksafety --config slice.json --slice incr slice.jazz 2>&1 | grep -o -e '^u64\[4\] [a-z]*' -e '^fn [a-z]*' -e '^Analyzing.*'
  fn incr
  Analyzing function incr
