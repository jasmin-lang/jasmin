(* Placement of the arguments of an export function.

   The calling convention gives a fixed number of registers for passing
   arguments; when a function has more arguments than that, the extra ones are
   passed by the caller on the stack, just below the stack pointer at the entry
   of the callee.

   The position of every argument is a function of the argument types and of the
   calling convention only; it is not stored anywhere. This is the single
   definition of that function: it is used by the linearization (which emits the
   loads of the stack arguments), by the assembly generation (which checks that
   the register arguments follow the convention) and, re-implemented, by the
   register allocation. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From Coq Require Import ZArith.
Require Import utils type.

Local Open Scope Z_scope.

Section STACK_ARGS.

Context {pd : PointerData}.

(* [stack_arg_positions nreg ofs0 tys] returns, for each type of [tys], [None]
   if the corresponding argument is passed in a register and [Some ofs] if it is
   passed on the stack, [ofs] being the offset with respect to the stack pointer
   at the entry of the function.

   [nreg] is the number of registers available for arguments and [ofs0] the
   offset of the first stack slot. Each stack argument occupies a full pointer-
   sized slot.

   Words wider than a pointer (vectors) are passed in vector registers: they
   never go to the stack and they do not consume a general-purpose argument
   register. Other types are not passed on the stack either; they are rejected
   elsewhere. *)
Fixpoint stack_arg_positions (nreg : nat) (ofs0 : Z) (tys : seq ltype) : seq (option Z) :=
  match tys with
  | [::] => [::]
  | ty :: tys =>
    match ty with
    | lword ws =>
      if (ws <= Uptr)%CMP then
        match nreg with
        | S nreg => None :: stack_arg_positions nreg ofs0 tys
        | O => Some ofs0 :: stack_arg_positions 0 (ofs0 + wsize_size Uptr) tys
        end
      else None :: stack_arg_positions nreg ofs0 tys
    | lbool => None :: stack_arg_positions nreg ofs0 tys
    end
  end.

Lemma size_stack_arg_positions n ofs tys :
  size (stack_arg_positions n ofs tys) = size tys.
Proof.
  elim: tys n ofs => [ | ty tys ih] n ofs //=.
  by case: ty => [ | ws] //=; [rewrite ih | case: ifP => _; [case: n => [ | n] | ]; rewrite /= ih].
Qed.

(* The offset of the first stack slot does not decide which arguments go to the
   stack. *)
Lemma stack_arg_positions_isSome nreg ofs0 ofs1 tys :
  [seq isSome o | o <- stack_arg_positions nreg ofs0 tys] =
  [seq isSome o | o <- stack_arg_positions nreg ofs1 tys].
Proof.
  elim: tys nreg ofs0 ofs1 => [ | ty tys ih] // nreg ofs0 ofs1.
  case: ty => [ | ws] /=; first by rewrite (ih nreg ofs0 ofs1).
  case: ifP => _ /=; last by rewrite (ih nreg ofs0 ofs1).
  case: nreg => [ | nreg] /=.
  + by rewrite (ih 0%nat (ofs0 + wsize_size Uptr)%Z (ofs1 + wsize_size Uptr)%Z).
  by rewrite (ih nreg ofs0 ofs1).
Qed.

End STACK_ARGS.
