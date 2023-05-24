require Gimli_arm Gimli_x86.
import List Int JWord.

equiv gimli_ref_equiv :
  Gimli_arm.M.gimli_ref ~ Gimli_x86.M.gimli_ref :
  ={ state } ==> ={ res }.
proof.
  proc.
  inline *; wp.
  pose k := 2654435584.
  while (={round, state} /\ rc{1} = W32.of_int k); wp.
  - by while (={column, state} /\ rc{1} = W32.of_int k); auto => /> /#.
  skip => />.
  by rewrite (W2u16.of_uint_pack2 k) (iotaS 0 1) // iota1.
qed.
