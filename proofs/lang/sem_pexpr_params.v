Require Import
  flag_combination
  sopn
  syscall
  wsize.


Class SemPexprParams (asm_op syscall_state : Type) := mk_spp
  {
    _pd :> PointerData | 1000;
    _asmop :> asmOp asm_op | 1000;
    _fcp :> FlagCombinationParams | 1000;
    _sc_sem :> syscall_sem syscall_state | 1000;
  }.

Arguments mk_spp {_ _ _ _ _ _}.
#[export]
Existing Instance mk_spp.

(* This "Hint Cut" allows to prune the paths in the typeclass search where
   we apply a field of SemPexprParams and then later the constructor
   mk_spp. This allows to put both fields and the constructor as instances
   and still avoid looping. *)
#[export]
Hint Cut [
  ( _ * )
  (_pd | _asmop | _fcp | _sc_sem)
  ( _ * )
  mk_spp
  ] : typeclass_instances.
