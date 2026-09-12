(* * Building blocks of the semantics of the operators [sop1], [sop2] and
   [opN], shared by the typed semantics ([sem_op_typed.v]) and, in the next
   commit, by the total semantics that lives here: the word shifts, the
   vector operations, the combination of flags and the array-initialisation
   predicates. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype div ssralg.
From mathcomp Require Import word_ssrZ.
Require Export type operators sem_type.
Require Export flag_combination.
Import Utf8.

(* -------------------------------------------------------------------- *)
(* Shifts on [Z]: the semantics of [Olsl Op_int] and [Oasr Op_int], and the
   integer counterpart of the shifts of the [wint] operators. *)

Definition zlsl (x i : Z) : Z :=
  if (0 <=? i)%Z then (x * 2^i)%Z
  else (x / 2^(-i))%Z.

Definition zasr (x i : Z) : Z :=
  zlsl x (-i).

(* -------------------------------------------------------------------- *)
(* ** Shifts and vector operations                                       *)
(* Shared by the typed and the total semantics. *)

Definition sem_shift (shift:forall {s}, word s -> Z -> word s) s (v:word s) (i:u8) :=
  let i :=  wunsigned i in
  shift v i.

Definition sem_shr {s} := @sem_shift (@wshr) s.
Definition sem_sar {s} := @sem_shift (@wsar) s.
Definition sem_shl {s} := @sem_shift (@wshl) s.
Definition sem_ror {s} := @sem_shift (@wror) s.
Definition sem_rol {s} := @sem_shift (@wrol) s.

Definition sem_vadd (ve:velem) {ws:wsize} := (lift2_vec ve +%w ws).
Definition sem_vsub (ve:velem) {ws:wsize} := (lift2_vec ve (fun x y => x - y)%w ws).
Definition sem_vmul (ve:velem) {ws:wsize} := (lift2_vec ve *%w ws).

Definition sem_vshr (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wshr x (wunsigned i)) ws v.

Definition sem_vsar (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wsar x (wunsigned i)) ws v.

Definition sem_vshl (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wshl x (wunsigned i)) ws v.

(* -------------------------------------------------------------------- *)
(* ** Binary operators                                                   *)

(* -------------------------------------------------------------------- *)
(* ** N-ary operators                                                    *)

Section WITH_PARAMS.

Context {cfcd : FlagCombinationParams}.

Definition sem_combine_flags (cf : combine_flags) (b0 b1 b2 b3 : bool) : bool :=
  cf_xsem negb andb orb (fun x y => x == y) b0 b1 b2 b3 cf.

End WITH_PARAMS.

(* -------------------------------------------------------------------- *)
(* ** The operators of the safety conditions                             *)

(* These are already total; they are here because [sopn_semi.v] interprets the
   conditions with the total semantics only. *)
Definition sem_opN_safety_typed (o: opN_safety) :
  let t := type_of_opN_safety o in
  let t := (map eval_atype t.1, eval_atype t.2) in
  sem_prod t.1 (exec (sem_t t.2)) :=
  match o with
  | Ois_arr_init alen =>
      fun (a:WArray.array _) (lo:Z) (len:Z) =>
        ok (all (WArray.is_init a) (ziota lo len))
  | Ois_barr_init alen =>
      fun (a:WArray.array _) (lo:Z) (len:Z) =>
        ok (all (WArray.is_initb a) (ziota lo len))
  end.
