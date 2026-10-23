- System calls (e.g., `#randombytes`) are no longer assumed to preserve the
  vector registers. Under `-call-conv windows`, an export function that issues
  a system call now saves and restores `ymm6` to `ymm15`, and a vector value
  can no longer stay in a register across a system call
  ([PR #1640](https://github.com/jasmin-lang/jasmin/pull/1640)).
