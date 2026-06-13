- Experimental register-allocation hints. These hints are best-effort: they are
  not part of the compiler correctness of Jasmin. The annotation is
  case-sensitive and uses architecture-specific register names: e.g., `RAX` on
  x86-64, `r0` on arm-m4, `x10`, `ra` on risc-v.  `#[force_regalloc=REG]`
forces a `reg` variable to the named register. For example, on x86-64:
  ```
  #[force_regalloc=RAX] reg u64 x;
  ```
