From mathcomp Require Import all_ssreflect all_algebra.
Require Import leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant div_leak_kind :=
| DLK_none
| DLK_num_log.

Definition build_div_leak dlk (s: signedness) (sz: wsize) (h l d: word sz) :=
  match dlk with
  | DLK_none => LEmpty
  | DLK_num_log =>
    let i := if s == Signed then wdwordu h l else wdwords h l in
    LIdx (Z.log2 (Z.abs i + 1))
  end.

Variant mem_leak_kind :=
| MLK_full
| MLK_div32
| MLK_div64.

Definition build_mem_leak mlk (p:pointer) :=
  match mlk with
  | MLK_full => p
  | MLK_div32 => wdiv p (wrepr Uptr 32)
  | MLK_div64 => wdiv p (wrepr Uptr 64)
  end.

Definition build_model (dlk: div_leak_kind) (mlk: mem_leak_kind) :=
  {| div_leak_ := build_div_leak dlk
   ; mem_leak_ := build_mem_leak mlk|}.
