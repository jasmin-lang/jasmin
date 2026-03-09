require import List.

type 'k trace_ = ('k * bool) list.

op valid ['k] (t : 'k trace_) = all snd t.

lemma valid_cat ['k] (x y : 'k trace_) :
  valid (x ++ y) <=> valid x /\ valid y.
proof. exact: all_cat. qed.


op trace ['k 'a] (x:'a * 'k trace_) = x.`2.

op validk ['k] (k : 'k) (t : 'k trace_) =
  with t = []       => true
  with t = p :: t' => if p.`1 = k then p.`2 /\ validk k t' else (p.`2 => validk k t').

lemma forall_validk_valid ['k] (t : 'k trace_) :
  (forall k, validk k t) => valid t.
proof.
  elim: t => //= -[k' b] t hrec /#.
qed.

lemma validk_cat ['k] (k : 'k) t1 t2 :
  validk k t1 =>
  (valid t1 => validk k t2) =>
  validk k (t1 ++ t2).
proof.
  elim t1 => //= -[k' b] t1 hrec /= /#.
qed.

type kind =
[
  | Assert
  | Assume
].

type trace = kind trace_.

lemma all_validk_valid t : validk Assert t => validk Assume t => valid t.
proof.
  by move=> *; apply forall_validk_valid => -[].
qed.
