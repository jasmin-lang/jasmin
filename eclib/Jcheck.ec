
require import AllCore IntDiv CoreMap List Distr.

type 'k trace_ = ('k * bool) list.

op trace ['k 'a] (x:'a * 'k trace_) = x.`2.

op valid ['k] (t : 'k trace_) = all (fun (p:_ * _) => p.`2) t.

op validk ['k] (k : 'k) (t : 'k trace_) =
  with t = []       => true
  with t = p :: t' => if p.`1 = k then p.`2 /\ validk k t' else (p.`2 => validk k t').

lemma valid_cat ['k] (t1 t2 : 'k trace_) : valid (t1 ++ t2) <=> valid t1 /\ valid t2.
proof. apply all_cat. qed.

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

(*
op validk' (k:kind) (t:trace) =
  with t = []       => true
  with t = p :: t' => if p.`2 then validk' k t' else !(p.`1 = k).

lemma equiv_vali k t : 
   validk k t <=> validkl k t.
proof.
  elim: t => //= -[k' b] t hrec /=.
  case: b => //.
qed.
*)

lemma all_validk_valid t : validk Assert t => validk Assume t => valid t.
proof.
  by move=> *; apply forall_validk_valid => -[].
qed.