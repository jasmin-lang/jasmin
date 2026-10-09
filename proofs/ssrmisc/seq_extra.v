From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From Coq Require Import Utf8.
Require Import oseq utils.


Section PairFoldLeft.

  Variables (T R : Type) (f : R -> T → T → R).

  Fixpoint pairfoldl z t s :=
    if s is x :: s'
    then pairfoldl (f z t x) x s'
    else z.

End PairFoldLeft.


Section MapProps.

End MapProps.


Section OnthProps.

End OnthProps.

Section AllProps.

End AllProps.
