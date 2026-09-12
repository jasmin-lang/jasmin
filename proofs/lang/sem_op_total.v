(* * Total semantics of the operators [sop1], [sop2] and [opN].

   For every operator this file gives a function of type
   [sem_prod tin (sem_t tout)]: no [exec], hence no failure. It is the same
   function as the typed semantics of [sem_op_typed.v] wherever the latter
   succeeds; where the typed semantics fails (the [wint] operators out of
   range, the divisions on words) the total one is the corresponding
   operation on words, i.e. modular arithmetic and unguarded division.

   The conditions under which the two agree are stated in [op_semi.v]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype div ssralg.
From mathcomp Require Import word_ssrZ.
Require Export type operators sem_type.
Require Export flag_combination.
Import Utf8.

(* -------------------------------------------------------------------- *)
(* ** Unary operators                                                    *)

(* Total counterpart of [sem_wiop1_typed]. Where the typed semantics fails
   ([WIwint_of_int] and [WIneg] on an out-of-range result) the value is the one
   of the corresponding operation on words, i.e. modular arithmetic. *)
Definition sem_wiop1_total (sign : signedness) (o: wiop1) :
  let t := type_of_wiop1 o in
  let t := (eval_atype t.1, eval_atype t.2) in
  sem_t t.1 -> sem_t t.2 :=
  match o with
  | WIwint_of_int sz => wrepr sz
  | WIint_of_wint sz => @int_of_word sign sz

  | WIword_of_wint sz => fun (w:word sz) => w
  | WIwint_of_word sz => fun (w:word sz) => w

  | WIwint_ext szo szi => @sem_word_extend sign szo szi

  | WIneg sz => -%w
  end.

Arguments sem_wiop1_total : clear implicits.

(* Total counterpart of [sem_sop1_typed]: the same functions, without the
   [ok]; only the [Owi1] cases really change. *)
Definition sem_sop1_total (o : sop1) :
  let t := type_of_op1 o in
  let t := (eval_atype t.1, eval_atype t.2) in
  sem_t t.1 -> sem_t t.2 :=
  match o with
  | Oword_of_int sz => wrepr sz
  | Oint_of_word sign sz => @int_of_word sign sz
  | Osignext szo szi => @sign_extend szo szi
  | Ozeroext szo szi => @zero_extend szo szi
  | Onot => negb
  | Olnot sz => @wnot sz
  | Oneg Op_int => Z.opp
  | Oneg (Op_w sz) => -%w
  | Owi1 sign o => sem_wiop1_total sign o
  end.

Arguments sem_sop1_total : clear implicits.

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

Definition mk_sem_wicmp_total sign sz (o:Z -> Z -> bool) (w1 w2 : word sz) : bool :=
  o (int_of_word sign w1) (int_of_word sign w2).

(* Total counterpart of [sem_wiop2_typed]. The arithmetic operations are the
   corresponding operations on words (modular arithmetic), the shifts are the
   word shifts and the divisions are the unguarded ones (division by zero is
   zero). *)
Definition sem_wiop2_total (sign : signedness) (sz : wsize) ( o : wiop2) :
  let t := type_of_wiop2 sz o in
  let t := (eval_atype t.1.1, eval_atype t.1.2, eval_atype t.2) in
  sem_t t.1.1 -> sem_t t.1.2 -> sem_t t.2 :=
  match o with

  | WIadd => +%w
  | WImul => *%w
  | WIsub => (fun x y =>  x - y)%w
  | WIdiv => signed (@wdiv sz) (@wdivi sz) sign
  | WImod => signed (@wmod sz) (@wmodi sz) sign

  | WIshl => @sem_shl sz
  | WIshr => signed (@sem_shr sz) (@sem_sar sz) sign

  | WIeq  => @mk_sem_wicmp_total sign sz Z.eqb
  | WIneq => @mk_sem_wicmp_total sign sz (fun z1 z2 => ~~ Z.eqb z1 z2)
  | WIlt  => @mk_sem_wicmp_total sign sz Z.ltb
  | WIle  => @mk_sem_wicmp_total sign sz Z.leb
  | WIgt  => @mk_sem_wicmp_total sign sz Z.gtb
  | WIge  => @mk_sem_wicmp_total sign sz Z.geb
  end.

Arguments sem_wiop2_total : clear implicits.

(* Total counterpart of [sem_sop2_typed]: the same functions, without the
   [ok]; only the divisions on words and the [Owi2] cases really change. *)
Definition sem_sop2_total (o: sop2) :
  let t := type_of_op2 o in
  let t := (eval_atype t.1.1, eval_atype t.1.2, eval_atype t.2) in
  sem_t t.1.1 -> sem_t t.1.2 -> sem_t t.2 :=
  match o with
  | Obeq => @eq_op bool
  | Oand => andb
  | Oor  => orb

  | Oadd Op_int     => Z.add
  | Oadd (Op_w s)   => +%w
  | Omul Op_int     => Z.mul
  | Omul (Op_w s)   => *%w
  | Osub Op_int     => Z.sub
  | Osub (Op_w s)   => (fun x y =>  x - y)%w
  | Odiv u Op_int   => signed Z.div Z.quot u
  | Odiv u (Op_w s) => signed (@wdiv s) (@wdivi s) u
  | Omod u Op_int   => signed Z.modulo Z.rem u
  | Omod u (Op_w s) => signed (@wmod s) (@wmodi s) u

  | Oland s       => @wand s
  | Olor  s       => @wor s
  | Olxor s       => @wxor s
  | Olsr s        => @sem_shr s
  | Olsl Op_int   => zlsl
  | Olsl (Op_w s) => @sem_shl s
  | Oasr Op_int   => zasr
  | Oasr (Op_w s) => @sem_sar s
  | Oror s        => @sem_ror s
  | Orol s        => @sem_rol s

  | Oeq Op_int    => Z.eqb
  | Oeq (Op_w s)  => eq_op
  | Oneq Op_int   => (fun x y => negb (Z.eqb x y))
  | Oneq (Op_w s) => (fun x y => (x != y))

  | Olt Cmp_int   => Z.ltb
  | Ole Cmp_int   => Z.leb
  | Ogt Cmp_int   => Z.gtb
  | Oge Cmp_int   => Z.geb

  | Olt (Cmp_w u s) => wlt u
  | Ole (Cmp_w u s) => wle u
  | Ogt (Cmp_w u s) => (fun x y => wlt u y x)
  | Oge (Cmp_w u s) => (fun x y => wle u y x)
  | Ovadd ve ws     => sem_vadd ve
  | Ovsub ve ws     => sem_vsub ve
  | Ovmul ve ws     => sem_vmul ve
  | Ovlsr ve ws     => sem_vshr ve
  | Ovlsl ve ws     => sem_vshl ve
  | Ovasr ve ws     => sem_vsar ve

  | Owi2 s sz o => sem_wiop2_total s sz o
  end.

Arguments sem_sop2_total : clear implicits.

(* -------------------------------------------------------------------- *)
(* ** N-ary operators                                                    *)

Section WITH_PARAMS.

Context {cfcd : FlagCombinationParams}.

Definition sem_combine_flags (cf : combine_flags) (b0 b1 b2 b3 : bool) : bool :=
  cf_xsem negb andb orb (fun x y => x == y) b0 b1 b2 b3 cf.

(* Total counterpart of [sem_opN_typed], which is already total
   ([sem_opN_typed_ok]); [WArray.fill] cannot fail on the length it is applied
   to, but the failure has to be discarded syntactically. *)
Definition sem_opN_total (o: opN) :
  let t := type_of_opN o in
  let t := (map eval_atype t.1, eval_atype t.2) in
  sem_prod t.1 (sem_t t.2) :=
  match o with
  | Opack sz pe =>
      let ty := curry (A := cint) (sz %/ pe) (λ vs, wpack sz pe vs) in
      ecast l (sem_prod l _) (esym (map_nseq _ _ _)) ty
  | Oarray len =>
      let ty := sem_prod_app (collect (Z.to_nat len) [::])
                  (λ vs : seq (sem_t (cword U8)), rdflt (WArray.empty _) (WArray.fill _ vs)) in
      ecast l (sem_prod l _) (esym (map_nseq _ _ _)) ty
  | Ocombine_flags cf =>
      fun b0 b1 b2 b3 => sem_combine_flags cf b0 b1 b2 b3
  end.

Arguments sem_opN_total : clear implicits.

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
