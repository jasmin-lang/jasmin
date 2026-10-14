- The addresses of the loads and stores are checked in assembly generation
  against the encodable forms of the architecture (arm-m4, armv8a, risc-v),
  and the error for an unencodable immediate or address lists the arguments
  of the instruction and the accepted forms
  ([PR #1638](https://github.com/jasmin-lang/jasmin/pull/1638)).
