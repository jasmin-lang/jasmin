From mathcomp Require Import ssreflect ssrfun ssrbool seq.
Require Import expr compiler_util.

Local Open Scope seq_scope.

(* ** The assertions removed

   The pass removes every assertion of the program; the rest of the code is
   unchanged. The contracts are kept: the semantics of the extraction ignores
   them. A program whose assertions all hold behaves as the program without
   them. *)

Section ASM_OP.

Context `{asmop:asmOp}.

Fixpoint drop_asserts_i (i : instr) : cmd :=
  let 'MkI ii ir := i in
  match ir with
  | Cassert _ => [::]
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Ccall _ _ _ => [:: i]
  | Cif e c1 c2 =>
    [:: MkI ii (Cif e (flatten (map drop_asserts_i c1)) (flatten (map drop_asserts_i c2)))]
  | Cfor x r c => [:: MkI ii (Cfor x r (flatten (map drop_asserts_i c)))]
  | Cwhile a c1 e ii_w c2 =>
    [:: MkI ii (Cwhile a (flatten (map drop_asserts_i c1)) e ii_w
                         (flatten (map drop_asserts_i c2)))]
  end.

Definition drop_asserts_c (c : cmd) : cmd := flatten (map drop_asserts_i c).

Section PROGT.
Context {pT : progT}.

Definition drop_asserts_fd (fd : fundef) : fundef :=
  with_body fd (drop_asserts_c (f_body fd)).

Definition drop_asserts_prog : prog -> prog := map_prog drop_asserts_fd.

End PROGT.

End ASM_OP.
