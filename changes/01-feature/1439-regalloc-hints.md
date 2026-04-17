- Experimental register-allocation hints. Both annotations are case-sensitive
  and use architecture-specific register names: e.g., `RAX` on x86-64, `r0` on
  arm-m4, `x10`, `ra` on risc-v.
  - `#[force_regalloc=REG]` forces a `reg` variable to the named register. For
    example, on x86-64:
    ```
    #[force_regalloc=RAX] reg u64 x;
    ```

  - `#[force_regalloc_conflict=REG]` forbids the allocator from choosing the
    named register for the variable. Multiple annotations of this form may
    be attached to a single variable to block several registers. For
    example, on arm-m4:
    ```
    #[force_regalloc_conflict=r0, force_regalloc_conflict=r1] reg u32 x;
    ```

