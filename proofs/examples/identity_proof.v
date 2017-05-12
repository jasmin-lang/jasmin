Require Import wp.
Require Import identity.

Import ssreflect.

Import Utf8.
Import seq.
Import Integers.
Import expr.
Import Ssem.

Goal
  ∀ v,
    match get_fundef program identity with
    | None => False
    | Some fd =>
      hoare program
            (λ s, s.(sevm).[x] = v)
            (f_body fd)
            (λ s, s.(sevm).[r] = v)
    end%vmap.

Import prog_notation.

Proof.
  move=> v.
  apply: hoare_by_wp.
  post_wp.
  subst. reflexivity.
Qed.

Goal
  ∀ v,
  hoare program
    (λ _, True)
    [:: MkI xH (Ccall  DoNotInline [:: Lvar x] identity [:: Pcast (Pconst v)]) ]
    (λ s, s.(sevm).[x] = I64.repr v)%vmap.
Proof.
  move=> v.
  apply: hoare_by_wp.
  post_wp.
Abort.
