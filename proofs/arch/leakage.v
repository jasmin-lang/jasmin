From mathcomp Require Import all_ssreflect all_algebra.
Require Import memory_model label.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope leakage_scope.
Delimit Scope leakage_scope with leakage.
Open Scope leakage_scope.

Section Leak_Asm.

Context {pd: PointerData}.

(** Leakage for assembly-level **)

Variant leak_asm : Type :=
  | Ljump  of seq pointer & remote_label  
  | Ljumpc of bool (* the value of the test *) 
  | Lop    of seq pointer.

Definition lempty := Lop [::].

End Leak_Asm.

Section Directive_Asm.

(** Directive for assembly-level **)
Variant directive_asm : Type :=
  | Dstep  : directive_asm
  | Dforce : directive_asm (* force directive : 
                              in case test evaluates to true, force always                                                  resembles taking else branch *).

End Directive_Asm.
