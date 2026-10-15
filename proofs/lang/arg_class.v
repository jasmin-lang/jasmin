(* Classes of the arguments of a function with respect to the calling
   convention: the arguments of a word type up to the size of a pointer are
   passed in general registers or on the stack, the larger ones (vectors) in
   vector registers. Register allocation must give to every parameter a register
   of the class of its declared type: this is what the assembly generation and
   the linearization rely on to compute the positions of the arguments. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import utils type var expr stack_args.

Section ARG_CLASS.

Context {pd : PointerData}.

Definition same_arg_class (ty ty' : ltype) : bool :=
  match ty, ty' with
  | lbool, lbool => true
  | lword ws, lword ws' => (ws <= Uptr)%CMP == (ws' <= Uptr)%CMP
  | _, _ => false
  end.

(* The variable [x] holds an argument of declared type [ty] in a register of the
   right class. *)
Definition arg_reg_class (ty : ltype) (x : var_i) : bool :=
  if ltype_of_atype (vtype x) is Some ty' then same_arg_class ty ty' else false.

(* Two lists of types of the same classes are passed at the same places. *)
Lemma stack_arg_positions_class tys tys' :
  all2 same_arg_class tys tys' ->
  forall nreg ofs,
    stack_arg_positions nreg ofs tys = stack_arg_positions nreg ofs tys'.
Proof.
  elim: tys tys' => [ | ty tys ih] [ | ty' tys'] //= /andP[] hty /ih {}ih nreg ofs.
  case: ty ty' hty => [ | ws] [ | ws'] //= => [ _ | /eqP hws ].
  + by rewrite ih.
  rewrite hws; case: ifP => _ /=; last by rewrite ih.
  by case: nreg => [ | n]; rewrite ih.
Qed.

End ARG_CLASS.
