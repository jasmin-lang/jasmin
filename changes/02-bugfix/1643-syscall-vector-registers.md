- System calls (e.g., `#randombytes`) are no longer assumed to preserve the
  vector registers, as the ABIs preserve them only in part. This only changes
  `-call-conv windows`: an export function that issues a
  system call, directly or through a local function, now saves and restores
  `ymm6` to `ymm15` (with AVX instructions, in a 32-byte aligned frame), so it
  may need a larger `#[callee_saved]` and can no longer use
  `#[stackalign=u128]`; and a vector value can no longer stay in a register
  across a system call (spill it explicitly)
  ([PR #1643](https://github.com/jasmin-lang/jasmin/pull/1643)).
