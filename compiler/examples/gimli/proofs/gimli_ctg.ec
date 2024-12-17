require Gimli_x86_ct Gimli_arm_ct Gimli_avx_ct.
from Jasmin require import JLeakage.

(** The [io] argument holds a pointer to the data that undergoes the permutation.
  * Since it is an address, its value is leaked, and should be public. *)

equiv gimli_x86_ct :
  Gimli_x86_ct.M.gimli ~ Gimli_x86_ct.M.gimli : ={ Gimli_x86_ct.M.leakages } ==> ={ Gimli_x86_ct.M.leakages }.
proof. proc; inline *; sim. qed.

equiv gimli_arm_ct :
  Gimli_arm_ct.M.gimli ~ Gimli_arm_ct.M.gimli : ={ Gimli_arm_ct.M.leakages } ==> ={ Gimli_arm_ct.M.leakages }.
proof. proc; inline *; sim. qed.

equiv gimli_avx_ct :
  Gimli_avx_ct.M.gimli ~ Gimli_avx_ct.M.gimli : ={ io, Gimli_avx_ct.M.leakages } ==> ={ Gimli_avx_ct.M.leakages }.
proof. proc; inline *; sim. qed.
