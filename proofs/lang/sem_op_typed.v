(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype div ssralg.
From mathcomp Require Import word_ssrZ.
Require Export type expr sem_type.
Require Export flag_combination.
Import Utf8.

Definition mk_sem_sop1 (t1 t2 : Type) (o:t1 -> t2) v1 : exec t2 :=
  ok (o v1).

Definition sem_wiop1_typed (sign : signedness) (o: wiop1) :
  let t := type_of_wiop1 o in
  sem_t t.1 → exec (sem_t t.2) :=
  match o return let t := type_of_wiop1 o in sem_t t.1 → exec (sem_t t.2) with
  | WIwint_of_int sz => wint_of_int sign sz
  | WIint_of_wint sz => mk_sem_sop1 (@int_of_word sign sz)

  | WIword_of_wint sz => mk_sem_sop1 (fun (w:word sz) => w)
  | WIwint_of_word sz => mk_sem_sop1 (fun (w:word sz) => w)

  | WIwint_ext szo szi => mk_sem_sop1 (@sem_word_extend sign szo szi)

  | WIneg sz => fun (w: word sz) => wint_of_int sign sz (- int_of_word sign w)
  end.

Arguments sem_wiop1_typed : clear implicits.

Definition sem_sop1_typed (o : sop1) :
  let t := type_of_op1 o in
  sem_t t.1 → exec (sem_t t.2) :=
  match o return let t := type_of_op1 o in sem_t t.1 → exec (sem_t t.2) with
  | Oword_of_int sz => mk_sem_sop1 (wrepr sz)
  | Oint_of_word sign sz => mk_sem_sop1 (@int_of_word sign sz)
  | Osignext szo szi => mk_sem_sop1 (@sign_extend szo szi)
  | Ozeroext szo szi => mk_sem_sop1 (@zero_extend szo szi)
  | Onot => mk_sem_sop1 negb
  | Olnot sz => mk_sem_sop1 (@wnot sz)
  | Oneg Op_int => mk_sem_sop1 Z.opp
  | Oneg (Op_w sz) => mk_sem_sop1 (-%R)%R
  | Owi1 sign o => sem_wiop1_typed sign o
  end.

Arguments sem_sop1_typed : clear implicits.

Definition zlsl (x i : Z) : Z :=
  if (0 <=? i)%Z then (x * 2^i)%Z
  else (x / 2^(-i))%Z.

Definition zasr (x i : Z) : Z :=
  zlsl x (-i).

Definition sem_shift (shift:forall {s}, word s -> Z -> word s) s (v:word s) (i:u8) :=
  let i :=  wunsigned i in
  shift v i.

Definition sem_shr {s} := @sem_shift (@wshr) s.
Definition sem_sar {s} := @sem_shift (@wsar) s.
Definition sem_shl {s} := @sem_shift (@wshl) s.
Definition sem_ror {s} := @sem_shift (@wror) s.
Definition sem_rol {s} := @sem_shift (@wrol) s.

Definition sem_vadd (ve:velem) {ws:wsize} := (lift2_vec ve +%R ws).
Definition sem_vsub (ve:velem) {ws:wsize} := (lift2_vec ve (fun x y => x - y)%R ws).
Definition sem_vmul (ve:velem) {ws:wsize} := (lift2_vec ve *%R ws).

Definition sem_vshr (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wshr x (wunsigned i)) ws v.

Definition sem_vsar (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wsar x (wunsigned i)) ws v.

Definition sem_vshl (ve:velem) {ws:wsize} (v : word ws) (i: u128) :=
  lift1_vec ve (fun x => wshl x (wunsigned i)) ws v.

Definition mk_sem_divmod (si: signedness) sz o (w1 w2: word sz) : exec (word sz) :=
  if ((w2 == 0) || [&& si == Signed, wsigned w1 == wmin_signed sz & w2 == -1])%R then Error ErrArith
  else ok (o w1 w2).

Definition mk_sem_sop2 (t1 t2 t3: Type) (o:t1 -> t2 -> t3) v1 v2 : exec t3 :=
  ok (o v1 v2).

Definition mk_sem_wiop2 sign sz (o:Z -> Z -> Z) (w1 w2 : word sz) : exec (word sz) :=
  wint_of_int sign sz (o (int_of_word sign w1) (int_of_word sign w2)).

Definition mk_sem_wishift sign sz (o:Z -> Z -> Z) (w1 : word sz) (w2 : word U8) : exec (word sz) :=
  wint_of_int sign sz (o (int_of_word sign w1) (int_of_word Unsigned w2)).

Definition mk_sem_wicmp sign sz (o:Z -> Z -> bool) (w1 w2 : word sz) : exec bool :=
  ok (o (int_of_word sign w1) (int_of_word sign w2)).

Definition sem_wiop2_typed (sign : signedness) (sz : wsize) ( o : wiop2) :
  let t := type_of_wiop2 sz o in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  match o return
   let t := type_of_wiop2 sz o in
   sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) with

  | WIadd => @mk_sem_wiop2 sign sz Z.add
  | WImul => @mk_sem_wiop2 sign sz Z.mul
  | WIsub => @mk_sem_wiop2 sign sz Z.sub
  | WIdiv => @mk_sem_divmod sign sz (signed wdiv wdivi sign)
  | WImod => @mk_sem_divmod sign sz (signed wmod wmodi sign)

  | WIshl => @mk_sem_wishift sign sz zlsl
  | WIshr => @mk_sem_wishift sign sz zasr

  | WIeq  => @mk_sem_wicmp sign sz Z.eqb
  | WIneq => @mk_sem_wicmp sign sz (fun z1 z2 => ~~ Z.eqb z1 z2)
  | WIlt  => @mk_sem_wicmp sign sz Z.ltb
  | WIle  => @mk_sem_wicmp sign sz Z.leb
  | WIgt  => @mk_sem_wicmp sign sz Z.gtb
  | WIge  => @mk_sem_wicmp sign sz Z.geb
  end.

Arguments sem_wiop2_typed : clear implicits.

Definition sem_sop2_typed (o: sop2) :
  let t := type_of_op2 o in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  match o with
  | Obeq => mk_sem_sop2 (@eq_op bool)
  | Oand => mk_sem_sop2 andb
  | Oor  => mk_sem_sop2 orb

  | Oadd Op_int     => mk_sem_sop2 Z.add
  | Oadd (Op_w s)   => mk_sem_sop2 +%R
  | Omul Op_int     => mk_sem_sop2 Z.mul
  | Omul (Op_w s)   => mk_sem_sop2 *%R
  | Osub Op_int     => mk_sem_sop2 Z.sub
  | Osub (Op_w s)   => mk_sem_sop2 (fun x y =>  x - y)%R
  | Odiv u Op_int   => mk_sem_sop2 (signed Z.div Z.quot u)
  | Odiv u (Op_w s) => @mk_sem_divmod u s (signed wdiv wdivi u)
  | Omod u Op_int   => mk_sem_sop2 (signed Z.modulo Z.rem u)
  | Omod u (Op_w s) => @mk_sem_divmod u s (signed wmod wmodi u)

  | Oland s       => mk_sem_sop2 wand
  | Olor  s       => mk_sem_sop2 wor
  | Olxor s       => mk_sem_sop2 wxor
  | Olsr s        => mk_sem_sop2 sem_shr
  | Olsl Op_int   => mk_sem_sop2 zlsl
  | Olsl (Op_w s) => mk_sem_sop2 sem_shl
  | Oasr Op_int   => mk_sem_sop2 zasr
  | Oasr (Op_w s) => mk_sem_sop2 sem_sar
  | Oror s        => mk_sem_sop2 sem_ror
  | Orol s        => mk_sem_sop2 sem_rol

  | Oeq Op_int    => mk_sem_sop2 Z.eqb
  | Oeq (Op_w s)  => mk_sem_sop2 eq_op
  | Oneq Op_int   => mk_sem_sop2 (fun x y => negb (Z.eqb x y))
  | Oneq (Op_w s) => mk_sem_sop2 (fun x y => (x != y))

  (* Fixme use the "new" Z *)
  | Olt Cmp_int   => mk_sem_sop2 Z.ltb
  | Ole Cmp_int   => mk_sem_sop2 Z.leb
  | Ogt Cmp_int   => mk_sem_sop2 Z.gtb
  | Oge Cmp_int   => mk_sem_sop2 Z.geb

  | Olt (Cmp_w u s) => mk_sem_sop2 (wlt u)
  | Ole (Cmp_w u s) => mk_sem_sop2 (wle u)
  | Ogt (Cmp_w u s) => mk_sem_sop2 (fun x y => wlt u y x)
  | Oge (Cmp_w u s) => mk_sem_sop2 (fun x y => wle u y x)
  | Ovadd ve ws     => mk_sem_sop2 (sem_vadd ve)
  | Ovsub ve ws     => mk_sem_sop2 (sem_vsub ve)
  | Ovmul ve ws     => mk_sem_sop2 (sem_vmul ve)
  | Ovlsr ve ws     => mk_sem_sop2 (sem_vshr ve)
  | Ovlsl ve ws     => mk_sem_sop2 (sem_vshl ve)
  | Ovasr ve ws     => mk_sem_sop2 (sem_vsar ve)

  | Owi2 s sz o => sem_wiop2_typed s sz o
  end.

Arguments sem_sop2_typed : clear implicits.

Section WITH_PARAMS.

Context {cfcd : FlagCombinationParams}.

Definition sem_combine_flags (cf : combine_flags) (b0 b1 b2 b3 : bool) : bool :=
  cf_xsem negb andb orb (fun x y => x == y) b0 b1 b2 b3 cf.

Definition sem_opN_typed (o: opN) :
  let t := type_of_opN o in
  sem_prod t.1 (exec (sem_t t.2)) :=
  match o with
  | Opack sz pe => curry (A := sint) (sz %/ pe) (λ vs, ok (wpack sz pe vs))
  | Ocombine_flags cf =>
      fun b0 b1 b2 b3 => ok (sem_combine_flags cf b0 b1 b2 b3)
  end.

End WITH_PARAMS.
