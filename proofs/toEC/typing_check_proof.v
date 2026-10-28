(* * Properties of the type checker [check_prog].

   They are stated as axioms. The branch type-safety of the Jasmin repository
   (proofs/compiler/typing_proof.v) proves the type safety of the checker in
   the partial semantics only: the evaluation of a well typed expression gives
   a value of its type, and a well typed program never raises [ErrType]. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem.
Require Import typing_check dead_code_total_proof.

(* A well typed program does not fail in the total mode on the code that
   [dead_code] and [dead_args] remove: its assignments and operators run on
   every state, the arguments of its calls have the types of the parameters,
   the destinations of its calls, the parameters and the results of its
   functions accept the values of their types. In the total mode the memory
   and array accesses and the operators do not fail and a variable never
   written reads the default value of its type: only a type mismatch could
   fail, which [check_prog] rules out. *)
Axiom check_prog_total_ok :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    (p : uprog),
  check_prog p = ok tt -> total_ok p.
