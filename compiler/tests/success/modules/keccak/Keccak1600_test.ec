require import AllCore IntDiv.


from Jasmin require import JModel_x86.


clone import PolyArray as Array25
 with op size <- 25.

clone import PolyArray as Array1234
 with op size <- 1234.


(********************************************************************)
theory Subreadwrite.

module Subreadwrite = {
 proc __mread_subu64(buf: W64.t, lEN tRAIL: int): W64.t*int*int*W64.t = {
  return witness;
 }
}.

abstract theory SRW_array.

op aSIZE: int.

clone import PolyArray as A_aSIZE
 with op size <- aSIZE.

module SRW_array = {
 proc __aread_subu64(buf: W8.t A_aSIZE.t, offset: W64.t, lEN tRAIL: int): int*int*int*W64.t = {
  return witness;
 }
}.

end SRW_array.

end Subreadwrite.

(********************************************************************)
theory Keccakf1600_generic.

(*require import Array25.*)
type keccak_state = W64.t Array25.t.

abbrev kECCAK_ROUNDS = 24.

end Keccakf1600_generic.

(********************************************************************)
theory Keccakf1600_ref.
export Keccakf1600_generic.

theory ANDN.
module ANDN = {
 proc __andn_64_bmi1(a b: W64.t): W64.t = {
  return witness;
 }
 proc __andn_64_nobmi1(a b: W64.t): W64.t = {
  return witness;
 }
}.
end ANDN.

(* this is a parametric module, but not an abstract theory! *)
theory KeccakF1600.

module type KeccakF1600_P = {
  proc aNDN(a b: W64.t): W64.t
}.

module KeccakF1600(P: KeccakF1600_P) = {
  proc _keccakf1600_ref(st: keccak_state): keccak_state = {
    return st;
  }
}.
end KeccakF1600.

theory Keccakf1600_bmi1.

module Keccakf1600_bmi1_pargs: KeccakF1600.KeccakF1600_P = {
 proc aNDN = ANDN.ANDN.__andn_64_bmi1
}.

module Keccakf1600_bmi1 = KeccakF1600.KeccakF1600(Keccakf1600_bmi1_pargs).

end Keccakf1600_bmi1.

theory Keccakf1600_nobmi1.

module Keccakf1600_nobmi1_pargs: KeccakF1600.KeccakF1600_P = {
 proc aNDN = ANDN.ANDN.__andn_64_nobmi1
}.

module Keccakf1600_nobmi1 = KeccakF1600.KeccakF1600(Keccakf1600_nobmi1_pargs).

end Keccakf1600_nobmi1.

end Keccakf1600_ref.


(********************************************************************)
theory Keccak1600_generic.

abbrev R72 = 72.

abbrev UNFINISHED = 0.
abbrev SHA3 = 6.

end Keccak1600_generic.

(********************************************************************)
theory Keccak1600_ref.
export Subreadwrite.
export Keccakf1600_ref.

(* this is a parametric module, but not an abstract theory! *)
theory Keccak1600ref_imem.

module type Keccak1600ref_imem_P = {
  proc kECCAK_F(st: keccak_state): keccak_state
}.

module Keccak1600ref_imem(P: Keccak1600ref_imem_P) = {
  proc _absorb__imem_ref(): unit = {
    return witness;
  }
}.

end Keccak1600ref_imem.

(* this parametric module gives rise to an abstract theory *)
abstract theory Keccak1600ref_array.
export Subreadwrite.

op aSIZE: int.

clone import PolyArray as A_aSIZE
 with op size <- aSIZE.

clone SRW_array as SRW
 with op aSIZE <- aSIZE,
      theory A_aSIZE <= A_aSIZE.

export SRW.

module type Keccak1600ref_array_P = {
  proc kECCAK_F(st: keccak_state): keccak_state
}.
module Keccak1600ref_array(P: Keccak1600ref_array_P) = {
  proc _absorb__array_ref(buf: W8.t A_aSIZE.t): keccak_state = {
    return witness;
  }
}.

end Keccak1600ref_array.


theory Keccak1600ref_imem_bmi1.

module Keccak1600ref_imem_bmi1_pargs: Keccak1600ref_imem.Keccak1600ref_imem_P = {
 proc kECCAK_F = Keccakf1600_bmi1.Keccakf1600_bmi1._keccakf1600_ref
}.

module Keccak1600ref_imem_bmi1 = Keccak1600ref_imem.Keccak1600ref_imem(Keccak1600ref_imem_bmi1_pargs).

end Keccak1600ref_imem_bmi1.


theory Keccak1600ref_imem_nobmi1.

module Keccak1600ref_imem_nobmi1_pargs: Keccak1600ref_imem.Keccak1600ref_imem_P = {
 proc kECCAK_F = Keccakf1600_nobmi1.Keccakf1600_nobmi1._keccakf1600_ref
}.

module Keccak1600ref_imem_nobmi1 = Keccak1600ref_imem.Keccak1600ref_imem(Keccak1600ref_imem_nobmi1_pargs).

end Keccak1600ref_imem_nobmi1.


abstract theory Keccak1600ref_array_bmi1.

op aSIZE: int.

clone import PolyArray as A_aSIZE
 with op size <- aSIZE.

clone Keccak1600ref_array as K1600ref_array
 with op aSIZE <- aSIZE,
      theory A_aSIZE <= A_aSIZE.

module Keccak1600ref_array_bmi1_pargs: K1600ref_array.Keccak1600ref_array_P = {
 proc kECCAK_F = Keccakf1600_bmi1.Keccakf1600_bmi1._keccakf1600_ref
}.


(*OBS: cannot use name from the theory K1600ref_array *)
module Keccak1600ref_array_bmi1 = K1600ref_array.Keccak1600ref_array(Keccak1600ref_array_bmi1_pargs).


end Keccak1600ref_array_bmi1.


abstract theory Keccak1600ref_array_nobmi1.

op aSIZE: int.

clone import PolyArray as A_aSIZE
 with op size <- aSIZE.

clone Keccak1600ref_array as K1600ref_array
 with op aSIZE <- aSIZE,
      theory A_aSIZE <= A_aSIZE.

module Keccak1600ref_array_nobmi1_pargs: K1600ref_array.Keccak1600ref_array_P = {
 proc kECCAK_F = Keccakf1600_nobmi1.Keccakf1600_nobmi1._keccakf1600_ref
}.


(*OBS: cannot use name from the theory K1600ref_array *)
module Keccak1600ref_array_nobmi1 = K1600ref_array.Keccak1600ref_array(Keccak1600ref_array_nobmi1_pargs).


end Keccak1600ref_array_nobmi1.

end Keccak1600_ref.

(********************************************************************)
theory Keccak1600_ref_test.
export Keccak1600_ref.



clone Keccak1600ref_array_bmi1 as A1234
 with op aSIZE <- 1234,
      theory A_aSIZE <= Array1234.

export Keccak1600ref_imem_bmi1.
export A1234.

print module Keccak1600ref_imem_bmi1.
print module A1234.Keccak1600ref_array_bmi1.

module Keccak1600_ref_test = {
 proc test_imem_absorb(): unit = {
  return witness;
 }
}.

end Keccak1600_ref_test.
