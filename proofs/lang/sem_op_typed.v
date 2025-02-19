(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype div ssralg.
From mathcomp Require Import word_ssrZ.
Require Export type expr sem_type.
Require Export flag_combination.
Import Utf8.

Class sem_sop_typed (sop1 sop2 : Type) :=
  { _type_of_op1 : sop1 -> stype * stype;
    _type_of_op2 : sop2 -> stype * stype * stype;
    _sem_sop1_typed : forall (o : sop1),
       let t := _type_of_op1 o in
       sem_t t.1 → exec (sem_t t.2);
    _sem_sop2_typed : forall (o : sop2),
       let t := _type_of_op2 o in
       sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2)
  }.

Definition sem_sop1_typed (o: sop1) :
  let t := type_of_op1 o in
  sem_t t.1 → sem_t t.2 :=
  match o with
  | Oword_of_int sz => wrepr sz
  | Oint_of_word sign sz => if sign is Unsigned then wunsigned else wsigned
  | Osignext szo szi => @sign_extend szo szi
  | Ozeroext szo szi => @zero_extend szo szi
  | Onot => negb
  | Olnot sz => wnot
  | Oneg Op_int => Z.opp
  | Oneg (Op_w sz) => (-%R)%R
  end.

Arguments sem_sop1_typed : clear implicits.

Definition mk_sem_sop1 (t1 t2 : Type) (o:t1 -> t2) v1 : exec t2 :=
  ok (o v1).

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

Definition signed {A:Type} (fu fs:A) s :=
  match s with
  | Unsigned => fu
  | Signed => fs
  end.

Definition mk_sem_divmod sz o (w1 w2: word sz) : exec (word sz) :=
  if ((w2 == 0) || ((wsigned w1 == wmin_signed sz) && (w2 == -1)))%R then Error ErrArith
  else ok (o w1 w2).

Definition mk_sem_sop2 (t1 t2 t3: Type) (o:t1 -> t2 -> t3) v1 v2 : exec t3 :=
  ok (o v1 v2).

Definition sem_sop2_typed (o: sop2) :
  let t := type_of_op2 o in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  match o with
  | Obeq => mk_sem_sop2 (@eq_op bool)
  | Oand => mk_sem_sop2 andb
  | Oor  => mk_sem_sop2 orb

  | Oadd Op_int      => mk_sem_sop2 Z.add
  | Oadd (Op_w s)    => mk_sem_sop2 +%R
  | Omul Op_int      => mk_sem_sop2 Z.mul
  | Omul (Op_w s)    => mk_sem_sop2 *%R
  | Osub Op_int      => mk_sem_sop2 Z.sub
  | Osub (Op_w s)    => mk_sem_sop2 (fun x y =>  x - y)%R
  | Odiv Cmp_int     => mk_sem_sop2 Z.div
  | Odiv (Cmp_w u s) => @mk_sem_divmod s (signed wdiv wdivi u)
  | Omod Cmp_int     => mk_sem_sop2 Z.modulo
  | Omod (Cmp_w u s) => @mk_sem_divmod s (signed wmod wmodi u)

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
  end.

Arguments sem_sop2_typed : clear implicits.

#[global]
Instance sem_sop_typed_core : sem_sop_typed sop1 sop2 :=
  {| _type_of_op1    := type_of_op1;
     _type_of_op2    := type_of_op2;
     _sem_sop1_typed := fun o w => ok (sem_sop1_typed o w);
     _sem_sop2_typed := sem_sop2_typed;
  |}.

Module SEO.

Import EO.

Definition in_uint_range (sz : wsize) z :=
  assert (Z.leb 0 z && Z.leb z (wmax_unsigned sz)) (ErrArith).

Definition in_sint_range (sz : wsize) z :=
  assert (Z.leb (wmin_signed sz) z && Z.leb z (wmax_signed sz)) (ErrArith).

Definition in_wi_range (wk : word_kind) (s : signedness) (sz : wsize) z :=
  if wk is Word then ok tt
  else signed in_uint_range in_sint_range s sz z.

Definition word_of_int (wk : word_kind) (s : signedness) (sz : wsize) (z : Z) :=
  Let _ := in_wi_range wk s sz z in
  ok (wrepr sz z).

Definition int_of_word (wk : word_kind) (s : signedness) (sz : wsize) (w : word sz) :=
  signed wunsigned wsigned s w.

Definition sem_word_extend (wk : word_kind) (s : signedness) (szo szi : wsize) :=
  signed (@zero_extend szo szi) (@sign_extend szo szi) s.

Definition mk_sem_w1
  (ow : forall sz, word sz -> word sz)
  (oz : Z -> Z)
  (k : op_kind) : sem_t (to_stype (t_opk k)) -> exec (sem_t (to_stype (t_opk k))) :=
  match k return sem_t (to_stype (t_opk k)) -> exec (sem_t (to_stype  (t_opk k))) with
  | Op_int => fun z => ok (oz z)
  | Op_w wk sign sz =>
    fun (w: word sz) =>
      if wk is Word then ok (ow sz w)
      else word_of_int wk sign sz (oz (int_of_word wk sign w))
  end.

Definition mk_sem_w2
  (ow : signedness -> forall sz, word sz -> word sz -> exec (word sz))
  (oz : Z -> Z -> Z)
  (k : op_kind) :
  sem_t (to_stype (t_opk k)) -> sem_t (to_stype (t_opk k)) -> exec (sem_t (to_stype (t_opk k))) :=
  match k return
    sem_t (to_stype (t_opk k)) -> sem_t (to_stype (t_opk k)) -> exec (sem_t (to_stype  (t_opk k)))
  with
  | Op_int => fun z1 z2 => ok (oz z1 z2)
  | Op_w wk sign sz =>
    fun (w1 w2: word sz) =>
      if wk is Word then ow sign sz w1 w2
      else word_of_int wk sign sz (oz (int_of_word wk sign w1) (int_of_word wk sign w2))
  end.

Definition sem_sop1_typed (o: sop1) :
  let t := type_of_op1 o in
  sem_t t.1 → exec (sem_t t.2) :=
  match o return
    let t := type_of_op1 o in sem_t t.1 → exec (sem_t t.2) with
  | Oword_of_int wk sign sz => word_of_int wk sign sz
  | Oint_of_word wk sign sz => mk_sem_sop1 (@int_of_word wk sign sz)

  | Oword_of_wint sign sz => mk_sem_sop1 (fun (w:word sz) => w)
  | Owint_of_word sign sz => mk_sem_sop1 (fun (w:word sz) => w)

  | Oword_ext wk sign szo szi => mk_sem_sop1 (@sem_word_extend wk sign szo szi)

  | Onot => mk_sem_sop1 negb
  | Olnot sz => mk_sem_sop1 wnot

  | Oneg k => @mk_sem_w1 (fun sz (w:word sz) => -w)%R Z.opp k
  end.

Arguments sem_sop1_typed : clear implicits.

Definition zshl (x i : Z) : Z :=
  if (0 <=? i)%Z then (x * 2^i)%Z
  else (x / 2^(-i))%Z.

Definition zshr (x i : Z) : Z :=
  zshl x (-i).

Definition wshr (s : signedness) : forall {s}, word s -> Z -> word s :=
  signed wshl wsar s.

Definition sem_shift
  (ow : signedness -> forall {sz}, word sz -> Z -> word sz)
  (oz : Z -> Z -> Z)
  (k : op_kind) :
  sem_t (to_stype (t_opk k)) -> sem_t (to_stype (t_opk (opku8 k))) -> exec (sem_t (to_stype (t_opk k))) :=
  match k return
    sem_t (to_stype (t_opk k)) -> sem_t (to_stype (t_opk (opku8 k))) -> exec (sem_t (to_stype  (t_opk k)))
  with
  | Op_int => fun z1 z2 => ok (oz z1 z2)
  | Op_w wk sign sz =>
    fun (w1 : word sz) (w2: word U8) =>
      let i := wunsigned w2 in
      if wk is Word then ok (ow sign w1 i)
      else
        word_of_int wk sign sz (oz (int_of_word wk sign w1) i)
  end.

Definition sem_shl k := @sem_shift (fun _ => @wshl) zshl k.
Definition sem_shr k := @sem_shift wshr zshr k.

Definition mk_sem_sop2 (t1 t2 t3: Type) (o:t1 -> t2 -> t3) v1 v2 : exec t3 :=
  ok (o v1 v2).

Definition mk_sem_cmp_w2
  (ow : forall {sz}, signedness -> word sz -> word sz -> bool)
  (oz : Z -> Z -> bool)
  (k : op_kind) :
  sem_t (to_stype (t_opk k)) -> sem_t (to_stype (t_opk k)) -> bool :=
  match k return
    sem_t (to_stype (t_opk k)) -> sem_t (to_stype (t_opk k)) -> bool
  with
  | Op_int => fun z1 z2 => oz z1 z2
  | Op_w wk sign sz =>
    fun (w1 w2: word sz) =>
      if wk is Word then ow sign w1 w2
      else oz (int_of_word wk sign w1) (int_of_word wk sign w2)
  end.

Definition sem_sop2_typed (o: sop2) :
  let t := type_of_op2 o in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  match o return
   let t := type_of_op2 o in
   sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) with
  | Obeq => mk_sem_sop2 (@eq_op bool)
  | Oand => mk_sem_sop2 andb
  | Oor  => mk_sem_sop2 orb

  | Oadd k => @mk_sem_w2 (fun _ sz (w1 w2 : word sz) => ok (w1 + w2))%R Z.add k
  | Omul k => @mk_sem_w2 (fun _ sz (w1 w2 : word sz) => ok (w1 * w2))%R Z.mul k
  | Osub k => @mk_sem_w2 (fun _ sz (w1 w2 : word sz) => ok (w1 - w2))%R Z.sub k

  | Odiv k => @mk_sem_w2 (fun sign sz => mk_sem_divmod (signed (@wdiv sz) (@wdivi sz) sign)) Z.div k
  | Omod k => @mk_sem_w2 (fun sign sz => mk_sem_divmod (signed (@wmod sz) (@wmodi sz) sign)) Z.modulo k

  | Oland sz => mk_sem_sop2 wand
  | Olor  sz => mk_sem_sop2 wor
  | Olxor sz => mk_sem_sop2 wxor
  | Oshl  k  => @sem_shl k
  | Oshr  k  => @sem_shr k
  | Oror s        => mk_sem_sop2 sem_ror
  | Orol s        => mk_sem_sop2 sem_rol

  | Oeq   k => mk_sem_sop2 (@mk_sem_cmp_w2 (fun sz _ (w1 w2: word sz) => w1 == w2) Z.eqb k)
  | Oneq  k =>
      mk_sem_sop2 (@mk_sem_cmp_w2
         (fun sz _ (w1 w2: word sz) => w1 != w2) (fun z1 z2 => ~~Z.eqb z1 z2) k)

  | Olt k => mk_sem_sop2 (@mk_sem_cmp_w2 (@wlt) Z.ltb k)
  | Ole k => mk_sem_sop2 (@mk_sem_cmp_w2 (@wle) Z.leb k)
  | Ogt k => mk_sem_sop2 (@mk_sem_cmp_w2 (fun sz sign x y => wlt sign y x) Z.gtb k)
  | Oge k => mk_sem_sop2 (@mk_sem_cmp_w2  (fun sz sign x y => wle sign y x) Z.geb k)

  | Ovadd ve ws     => mk_sem_sop2 (sem_vadd ve)
  | Ovsub ve ws     => mk_sem_sop2 (sem_vsub ve)
  | Ovmul ve ws     => mk_sem_sop2 (sem_vmul ve)
  | Ovlsr ve ws     => mk_sem_sop2 (sem_vshr ve)
  | Ovlsl ve ws     => mk_sem_sop2 (sem_vshl ve)
  | Ovasr ve ws     => mk_sem_sop2 (sem_vsar ve)
  end.

Arguments sem_sop2_typed : clear implicits.

End SEO.

#[local]
Instance sem_sop_typed_EO : sem_sop_typed EO.sop1 EO.sop2 :=
  {| _type_of_op1    := EO.type_of_op1;
     _type_of_op2    := EO.type_of_op2;
     _sem_sop1_typed := SEO.sem_sop1_typed;
     _sem_sop2_typed := SEO.sem_sop2_typed;
  |}.

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
