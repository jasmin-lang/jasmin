require import List.

type 'k trace_ = ('k * bool) list.

op valid ['k] (t : 'k trace_) = all snd t.

lemma valid_cat ['k] (x y : 'k trace_) :
  valid (x ++ y) <=> valid x /\ valid y.
proof. exact: all_cat. qed.

type kind =
[
  | Assert
  | Assume
].

type trace = kind trace_.
