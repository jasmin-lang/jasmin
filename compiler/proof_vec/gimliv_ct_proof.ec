require import Jasmin_model Gimliv_ct.

(* [state] is a pointer allowing to initialize the state of gimli *)
(* Since it is an address, its value is leak, and should be public *)
equiv gimli_ct : M.gimli ~ M.gimli : ={state, M.leakages} ==> ={M.leakages}.
proof.
  proc; inline *; sim.
qed.

