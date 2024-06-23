require Gimli_arm Gimli_x86.
import List Int JWord.

equiv gimli_equiv :
  Gimli_arm.M.gimli ~ Gimli_x86.M.gimli :
  ={ state } ==> ={ res }.
proof.
  proc.
  inline *; wp.
  pose k := 2654435584.
  while (={round, state} /\ rc{1} = W32.of_int k); wp; last by auto.
  by while (={column, state} /\ rc{1} = W32.of_int k); auto => /> /#.
qed.
