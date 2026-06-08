- Add `overlay` annotation allowing to force the compiler to share different stack arrays, possibly of different size.
  ``` #[overlay = t] stack u32[2] t1;
      #[overlay = t] stack u64[3] t2;
      #[overlay = u] stack u16[5] u1;
      #[overlay = u] stack u16[3] u2;
  ```
  In this case, `t1` and `t2` (resp. `u1` and `u2`) will be allocated to the same stack region.
  ([PR 1475](https://github.com/jasmin-lang/jasmin/pull/1475)).