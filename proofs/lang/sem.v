(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export array expr gen_map leakage low_memory warray_ sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ** Values
  * -------------------------------------------------------------------- *)

Variant value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall len, WArray.array len -> value
  | Vword  : forall s, word s -> value
  | Vundef : stype -> value.

Definition undef_b := Vundef sbool.

Definition values := seq value.

Definition to_bool v :=
  match v with
  | Vbool b      => ok b
  | Vundef sbool => undef_error
  | _            => type_error
  end.

Definition to_int v :=
  match v with
  | Vint z      => ok z
  | Vundef sint => undef_error
  | _           => type_error
  end.

Definition truncate_word (s s':wsize) (w:word s') : exec (word s) :=
   if (s <= s')%CMP then ok (zero_extend s w) else type_error.

Definition to_word (s: wsize) (v: value) : exec (word s) :=
  match v with
  | Vword s' w        => truncate_word s w
  | Vundef (sword s') => Error (if (s <= s')%CMP then ErrAddrUndef else ErrType)
  | _                 => type_error
  end.

Notation to_pointer := (to_word Uptr).

Definition to_arr len v : exec (sem_t (sarr len)) :=
  match v with
  | Varr len' t => WArray.cast len t
  | Vundef (sarr len') =>
    Error (if (len <=? len')%Z then ErrAddrUndef else ErrType)
  | _ => type_error
  end.

Definition vundef_type (t:stype) :=
  match t with
  | sword _ => sword8
  | sarr _  => sarr 1
  | _       => t
  end.

Definition type_of_val (v:value) : stype :=
  match v with
  | Vbool _     => sbool
  | Vint  _     => sint
  | Varr n _    => sarr n
  | Vword s _   => sword s
  | Vundef t    => vundef_type t
  end.

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool   => to_bool
  | sint    => to_int
  | sarr n  => to_arr n
  | sword s => to_word s
  end.

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | sbool   => Vbool
  | sint    => Vint
  | sarr n  => @Varr n
  | sword s => @Vword s
  end.

Definition truncate_val (ty: stype) (v: value) : exec value :=
  of_val ty v >>= λ x, ok (to_val x).

Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
Proof. by case: t s. Qed.

Definition oto_val t : sem_ot t -> value :=
  match t return sem_ot t -> value with
  | sbool => fun ob => if ob is Some b then Vbool b else Vundef sbool
  | x     => @to_val x
  end.

Lemma type_of_oto_val t (s: sem_ot t) : type_of_val (oto_val s) = t.
Proof. by case: t s => //= -[]. Qed.

(* -------------------------------------------------------------------- *)
Definition subtype (t t': stype) :=
  match t with
  | sword w => if t' is sword w' then (w ≤ w')%CMP else false
  | sarr n =>
    if t' is sarr n' then (n <=? n')%Z else false
  | _ => t == t'
  end.

Lemma subtypeE ty ty' :
  subtype ty ty' →
  match ty' with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | sarr n'   => ∃ n, ty = sarr n ∧ (n <= n')%Z
  | _         => ty = ty'
end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /ZleP ?; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtypeEl ty ty' :
  subtype ty ty' →
  match ty with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | sarr n   => ∃ n', ty' = sarr n' ∧ (n <= n')%Z
  | _        => ty' = ty
  end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /ZleP ?; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtype_refl x : subtype x x.
Proof. case: x => //= ?;apply Z.leb_refl. Qed.
Hint Resolve subtype_refl : core.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|n1|sx] //.
  + case: y => //= n2 /ZleP h1;case: z => //= n3 /ZleP h2.
    by apply /ZleP;apply: Z.le_trans h1 h2.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

Definition check_ty_val (ty:stype) (v:value) :=
  subtype ty (type_of_val v).

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t (fun t => exec (sem_t t))).

Definition undef_addr t :=
  match t return exec (sem_t t) with
  | sbool | sint | sword _ => undef_error
  | sarr n => ok (WArray.empty n)
  end.

Definition vmap0 : vmap :=
  @Fv.empty (fun t => exec (sem_t t)) (fun x => undef_addr x.(vtype)).

Definition on_vu t r (fv: t -> r) (fu:exec r) (v:exec t) : exec r :=
  match v with
  | Ok v => ok (fv v)
  | Error ErrAddrUndef => fu
  | Error e            => Error e
  end.

Lemma on_vuP T R (fv: T -> R) (fu: exec R) (v:exec T) r P:
  (forall t, v = ok t -> fv t = r -> P) ->
  (v = undef_error -> fu = ok r -> P) ->
  on_vu fv fu v = ok r -> P.
Proof. by case: v => [a | []] Hfv Hfu //=;[case; apply: Hfv | apply Hfu]. Qed.

(* An access to a undefined value, leads to an error *)
Definition get_var (m:vmap) x :=
  on_vu (@to_val (vtype x)) undef_error (m.[x]%vmap).

(* Assigning undefined value is allowed only for bool *)
Definition set_var (m:vmap) x v : exec vmap :=
  on_vu (fun v => m.[x<-ok v]%vmap)
        (if is_sbool x.(vtype) then ok m.[x<-undef_addr x.(vtype)]%vmap
         else type_error)
        (of_val (vtype x) v).

Lemma set_varP (m m':vmap) x v P :
   (forall t, of_val (vtype x) v = ok t -> m.[x <- ok t]%vmap = m' -> P) ->
   ( is_sbool x.(vtype) -> of_val (vtype x) v = undef_error ->
     m.[x<-undef_addr x.(vtype)]%vmap = m' -> P) ->
   set_var m x v = ok m' -> P.
Proof.
  move=> H1 H2;apply on_vuP => //.
  by case:ifPn => // hb herr []; apply : H2.
Qed.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition sem_shift (shift:forall {s}, word s -> Z -> word s) s (v:word s) (i:u8) :=
  let i :=  wunsigned (wand i (x86_shift_mask s)) in
  shift v i.

Definition sem_shr {s} := @sem_shift (@wshr) s.
Definition sem_sar {s} := @sem_shift (@wsar) s.
Definition sem_shl {s} := @sem_shift (@wshl) s.

Definition sem_vadd (ve:velem) {ws:wsize} := (lift2_vec ve +%R ws).
Definition sem_vsub (ve:velem) {ws:wsize} := (lift2_vec ve (fun x y => x - y)%R ws).
Definition sem_vmul (ve:velem) {ws:wsize} := (lift2_vec ve *%R ws).

Definition sem_vshr (ve:velem) {ws:wsize} (v : word ws) (i:u8) :=
  lift1_vec ve (fun x => wshr x (wunsigned i)) ws v.

Definition sem_vsar (ve:velem) {ws:wsize} (v : word ws) (i:u8) :=
  lift1_vec ve (fun x => wsar x (wunsigned i)) ws v.

Definition sem_vshl (ve:velem) {ws:wsize} (v : word ws) (i:u8) :=
  lift1_vec ve (fun x => wshl x (wunsigned i)) ws v.

Definition sem_sop1_typed (o: sop1) :
  let t := type_of_op1 o in
  sem_t t.1 → sem_t t.2 :=
  match o with
  | Oword_of_int sz => wrepr sz
  | Oint_of_word sz => wunsigned
  | Osignext szo szi => @sign_extend szo szi
  | Ozeroext szo szi => @zero_extend szo szi
  | Onot => negb
  | Olnot sz => wnot
  | Oneg Op_int => Z.opp
  | Oneg (Op_w sz) => (-%R)%R
  end.

Arguments sem_sop1_typed : clear implicits.

Definition sem_sop1 (o: sop1) (v: value) : exec value :=
  let t := type_of_op1 o in
  Let x := of_val _ v in
  ok (to_val (sem_sop1_typed o x)).

Lemma sem_sop1I y x f:
  sem_sop1 f x = ok y →
  exists2 w : sem_t (type_of_op1 f).1,
    of_val _ x = ok w &
    y = to_val (sem_sop1_typed f w).
Proof. by rewrite /sem_sop1; t_xrbindP => w ok_w <-; eauto. Qed.

Definition signed {A:Type} (fu fs:A) s :=
  match s with
  | Unsigned => fu
  | Signed => fs
  end.

Definition mk_sem_divmod sz o (w1 w2: word sz) : exec (word sz) :=
  if ((w2 == 0) || ((wsigned w1 == wmin_signed sz) && (w2 == -1)))%R then type_error
  else ok (o w1 w2).

Definition mk_sem_sop2 (t1 t2 t3: Type) (o:t1 -> t2 -> t3) v1 v2 : exec t3 :=
  ok (o v1 v2).

Definition sem_sop2_typed (o: sop2) :
  let t := type_of_op2 o in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  match o with
  | Oand => mk_sem_sop2 andb
  | Oor  => mk_sem_sop2 orb

  | Oadd Op_int   => mk_sem_sop2 Z.add
  | Oadd (Op_w s) => mk_sem_sop2 +%R
  | Omul Op_int   => mk_sem_sop2 Z.mul
  | Omul (Op_w s) => mk_sem_sop2 *%R
  | Osub Op_int   => mk_sem_sop2 Z.sub
  | Osub (Op_w s) => mk_sem_sop2 (fun x y =>  x - y)%R
  | Odiv Cmp_int  => mk_sem_sop2 Z.div
  | Odiv (Cmp_w u s) => @mk_sem_divmod s (signed wdiv wdivi u)
  | Omod Cmp_int  => mk_sem_sop2 Z.modulo
  | Omod (Cmp_w u s) => @mk_sem_divmod s (signed wmod wmodi u)

  | Oland s => mk_sem_sop2 wand
  | Olor  s => mk_sem_sop2 wor
  | Olxor s => mk_sem_sop2 wxor
  | Olsr  s => mk_sem_sop2 sem_shr
  | Olsl  s => mk_sem_sop2 sem_shl
  | Oasr  s => mk_sem_sop2 sem_sar

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

Definition sem_sop2 (o: sop2) (v1 v2: value) : exec value :=
  let t := type_of_op2 o in
  Let x1 := of_val _ v1 in
  Let x2 := of_val _ v2 in
  Let r  := sem_sop2_typed o x1 x2 in
  ok (to_val r).

Lemma sem_sop2I v v1 v2 f:
  sem_sop2 f v1 v2 = ok v →
  ∃ (w1 : sem_t (type_of_op2 f).1.1) (w2 : sem_t (type_of_op2 f).1.2)
    (w3: sem_t (type_of_op2 f).2),
    [/\ of_val _ v1 = ok w1,
        of_val _ v2 = ok w2,
        sem_sop2_typed f w1 w2 = ok w3 &
        v = to_val w3].
Proof.
  by rewrite /sem_sop2; t_xrbindP => w1 ok_w1 w2 ok_w2 w3 ok_w3 <- {v}; exists w1, w2, w3.
Qed.

Fixpoint app_sopn T ts : sem_prod ts (exec T) → values → exec T :=
  match ts return sem_prod ts (exec T) → values → exec T with
  | [::] => λ (o : exec T) (vs: values), if vs is [::] then o else type_error
  | t :: ts => λ (o: sem_t t → sem_prod ts (exec T)) (vs: values),
    if vs is v :: vs
    then Let v := of_val t v in app_sopn (o v) vs
    else type_error
  end.

Arguments app_sopn {T} ts _ _.

Definition curry A B (n: nat) (f: seq (sem_t A) → B) : sem_prod (nseq n A) B :=
  (fix loop n :=
   match n return seq (sem_t A) → sem_prod (nseq n A) B with
   | 0 => f
   | n'.+1 => λ acc a, loop n' (a :: acc)
   end) n [::].

Definition sem_opN_typed (o: opN) :
  let t := type_of_opN o in
  sem_prod t.1 (exec (sem_t t.2)) :=
  match o with
  | Opack sz pe => curry (A := sint) (sz %/ pe) (λ vs, ok (wpack sz pe vs))
  end.

Definition sem_opN (op: opN) (vs: values) : exec value :=
  Let w := app_sopn _ (sem_opN_typed op) vs in
  ok (to_val w).

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition on_arr_var A (s:estate) (x:var) (f:forall n, WArray.array n -> exec A) :=
  Let v := get_var s.(evm) x in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

Notation "'Let' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@on_arr_var _ s x (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Lemma on_arr_varP A (f : forall n, WArray.array n -> exec A) v s x P:
  (forall n t, vtype x = sarr n ->
               get_var (evm s) x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var s x f = ok v -> P.
Proof.
  rewrite /on_arr_var=> H;apply: rbindP => vx.
  case: x H => -[ | | n | sz ] nx;rewrite /get_var => H;
    case Heq : ((evm s).[_])%vmap => [v' | e] //=.
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]; apply: H => //;rewrite Heq. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
Qed.

Definition Varr_inj n n' t t' (e: @Varr n t = @Varr n' t') :
  ∃ (en: n = n'),
      eq_rect n (λ s, WArray.array s) t n' en = t' :=
  let 'Logic.eq_refl := e in
    (ex_intro _ erefl erefl).

Lemma Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
Proof.
  by move => /Varr_inj [en ]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec en erefl).
Qed.

Definition Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Definition get_global gd g : exec value :=
  Let w := get_global_word gd g in
  ok (Vword w).

Lemma get_globalI gd g v :
  get_global gd g = ok v →
  exists2 z : Z, get_global_Z gd g = Some z & v = Vword (wrepr (size_of_global g) z).
Proof.
  rewrite /get_global /get_global_word; case: get_global_Z => // z [<-];eauto.
Qed.

Definition is_defined (v: value) : bool :=
  if v is Vundef _ then false else true.

Section SEM_PEXPR.

Context (gd: glob_decls).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec (value * leak_e)  :=
 match e with
  | Pconst z => ok (Vint z, LEmpty)
  | Pbool b  => ok (Vbool b, LEmpty)
  | Parr_init n => ok (Varr (WArray.empty n), LEmpty)
  | Pvar x => Let v := get_var s.(evm) x in 
              ok (v, LEmpty)
  | Pglobal g => Let v := get_global gd g in 
                 ok (v, LEmpty)
  | Pget ws x e =>
      Let (n, t) := s.[x] in
      Let vl := sem_pexpr s e in 
      Let i := to_int vl.1 in 
      Let w := WArray.get ws t i in
      ok ((Vword w), LSub [ :: vl.2 ; (LIdx i)])
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let vl2 := sem_pexpr s e in 
    Let w2 := to_pointer vl2.1 in
    let adr := (w1 + w2)%R in 
    Let w  := read_mem s.(emem) adr sz in
    ok (@to_val (sword sz) w, LSub [ :: vl2.2;  (LAdr adr)])
  | Papp1 o e1 =>
    Let vl := sem_pexpr s e1 in
    Let v := sem_sop1 o vl.1 in 
    ok (v, vl.2)
  | Papp2 o e1 e2 =>
    Let vl1 := sem_pexpr s e1 in
    Let vl2 := sem_pexpr s e2 in
    Let v := sem_sop2 o vl1.1 vl2.1 in
    ok (v, LSub [:: vl1.2; vl2.2])
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    Let v := sem_opN op (unzip1 vs) in
    ok (v, LSub (unzip2 vs))
  | Pif t e e1 e2 =>
    Let vl := sem_pexpr s e in
    Let b := to_bool vl.1in
    Let vl1 := sem_pexpr s e1 in
    Let vl2 := sem_pexpr s e2 in
    Let v1 := truncate_val t vl1.1 in
    Let v2 := truncate_val t vl2.1 in
    ok (if b then v1 else v2, LSub [:: vl.2 ; vl1.2; vl2.2])
  end.

Definition sem_pexprs s es := mapM (sem_pexpr s) es.    

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok ({| emem := s.(emem); evm := vm |}).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s:estate) ty v :=
  on_vu (fun v => s) (if is_sbool ty then ok s else type_error)
          (of_val ty v).

Definition write_lval (l:lval) (v:value) (s:estate) : exec (estate * leak_e) :=
  match l with
  | Lnone _ ty => Let x := write_none s ty v in ok (x, LEmpty)
  | Lvar x => Let v' := write_var x v s in ok(v', LEmpty)
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let vl := sem_pexpr s e in 
    Let ve := to_pointer vl.1 in
    let p := (vx + ve)%R in
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok ({| emem := m;  evm := s.(evm) |}, LSub [:: vl.2; (LAdr p)])
  | Laset ws x i =>
    Let (n,t) := s.[x] in
    Let vl := sem_pexpr s i in 
    Let i := to_int vl.1 in
    Let v := to_word ws v in
    Let t := WArray.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |}, LSub [:: vl.2; (LIdx i)])
  end.

Fixpoint write_lvals (s:estate) xs vs : exec (estate * seq leak_e) :=
  match xs, vs with
  | [::], [::] => ok (s, [::])
  | x::xs, v::vs =>
    Let sl := write_lval x v s in
    Let sls := write_lvals sl.1 xs vs in
    ok (sls.1, sl.2::sls.2)
  | _, _ => Error ErrType                     
  end.

End SEM_PEXPR.


(* ---------------------------------------------------------------- *)
Definition is_word (sz: wsize) (v: value) : exec unit :=
  match v with
  | Vword _ _
  | Vundef (sword _)
    => ok tt
  | _ => type_error end.

Lemma is_wordI sz v u :
  is_word sz v = ok u →
  subtype (vundef_type (sword sz)) (type_of_val v).
Proof. case: v => // [ sz' w | [] // ] _; exact: wsize_le_U8. Qed.

(* ---------------------------------------------------------------- *)

Fixpoint list_ltuple (ts:list stype) : sem_tuple ts -> values :=
  match ts return sem_tuple ts -> values with
  | [::] => fun (u:unit) => [::]
  | t :: ts =>
    let rec := @list_ltuple ts in
    match ts return (sem_tuple ts -> values) -> sem_tuple (t::ts) -> values with
    | [::] => fun _ x => [:: oto_val x]
    | t1 :: ts' =>
      fun rec (p : sem_ot t * sem_tuple (t1 :: ts')) =>
       oto_val p.1 :: rec p.2
    end rec
  end.

Definition exec_sopn (o:sopn) (vs:values) : exec values :=
  let semi := sopn_sem o in
  Let t := app_sopn _ semi vs in
  ok (list_ltuple t).

Lemma type_of_val_ltuple tout (p : sem_tuple tout) :
  List.map type_of_val (list_ltuple p) = tout.
Proof.
  elim: tout p => //= t1 [|t2 tout] /=.
  + by rewrite /sem_tuple /= => _ x;rewrite type_of_oto_val.
  by move=> hrec [] x xs /=; rewrite type_of_oto_val hrec.
Qed.

Lemma sopn_toutP o vs vs' : exec_sopn o vs = ok vs' ->
  List.map type_of_val vs' = sopn_tout o.
Proof.
  rewrite /exec_sopn /sopn_tout /sopn_sem.
  t_xrbindP => p _ <-;apply type_of_val_ltuple.
Qed.

Section SEM.

Variable P:prog.

Notation gd := (p_globs P).

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let vl1 := sem_pexpr gd s pe1 in 
  Let i1 := to_int vl1.1 in 
  Let vl2 := sem_pexpr gd s pe2 in 
  Let i2 := to_int vl2.1 in
  ok (wrange d i1 i2, LSub [:: vl1.2 ; vl2.2]).

Definition sem_sopn gd o m lvs args := 
  Let vas := sem_pexprs gd m args in
  Let vs := exec_sopn o (unzip1 vas) in 
  Let ml := write_lvals gd m lvs vs in
  ok (ml.1, LSub [:: LSub (unzip2 vas) ; LSub ml.2]).

Inductive sem : estate -> cmd -> leak_c -> estate -> Prop :=
| Eskip s :
    sem s [::] [::] s

| Eseq s1 s2 s3 i c li lc :
    sem_I s1 i li s2 -> sem s2 c lc s3 -> sem s1 (i::c) (li :: lc) s3

with sem_I : estate -> instr -> leak_i -> estate -> Prop :=
| EmkI ii i s1 s2 li:
    sem_i s1 i li s2 ->
    sem_I s1 (MkI ii i) li s2

with sem_i : estate -> instr_r -> leak_i -> estate -> Prop :=
| Eassgn s1 s2 (x:lval) tag ty e v v' l1 l2:
    sem_pexpr gd s1 e = ok (v,l1)  ->
    truncate_val ty v = ok v' →
    write_lval gd x v' s1 = ok (s2, l2) ->
    sem_i s1 (Cassgn x tag ty e) (Lopn (LSub [:: l1 ; l2])) s2

| Eopn s1 s2 t o xs es lo:
    sem_sopn gd o s1 xs es = ok (s2, lo) ->
    sem_i s1 (Copn xs t o es) (Lopn lo) s2

| Eif_true s1 s2 e c1 c2 le lc:
    sem_pexpr gd s1 e = ok (Vbool true, le) ->
    sem s1 c1 lc s2 ->
    sem_i s1 (Cif e c1 c2) (Lcond le true lc) s2

| Eif_false s1 s2 e c1 c2 le lc:
    sem_pexpr gd s1 e = ok (Vbool false, le) ->
    sem s1 c2 lc s2 ->
    sem_i s1 (Cif e c1 c2) (Lcond le false lc) s2

| Ewhile_true s1 s2 s3 s4 a c e c' lc le lc' lw:
    sem s1 c lc s2 ->
    sem_pexpr gd s2 e = ok (Vbool true, le) ->
    sem s2 c' lc' s3 ->
    sem_i s3 (Cwhile a c e c') lw s4 ->
    sem_i s1 (Cwhile a c e c') (Lwhile_true lc le lc' lw) s4

| Ewhile_false s1 s2 a c e c' lc le:
    sem s1 c lc s2 ->
    sem_pexpr gd s2 e = ok (Vbool false, le) ->
    sem_i s1 (Cwhile a c e c') (Lwhile_false lc le) s2

| Efor s1 s2 (i:var_i) r c wr lr lf:
    sem_range s1 r = ok (wr, lr) ->
    sem_for i wr s1 c lf s2 ->
    sem_i s1 (Cfor i r c) (Lfor lr lf) s2

| Ecall s1 m2 s2 ii xs f args vargs vs lf l2:
    sem_pexprs gd s1 args = ok vargs ->
    sem_call s1.(emem) f (unzip1 vargs) lf m2 vs ->
    write_lvals gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok (s2, l2) ->
    sem_i s1 (Ccall ii xs f args) (Lcall (LSub (unzip2 vargs)) lf (LSub l2)) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> leak_for -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c [::] s

| EForOne s1 s1' s2 s3 i w ws c lc lw :
    write_var i (Vint w) s1 = ok s1' ->
    sem s1' c lc s2 ->
    sem_for i ws s2 c lw s3 ->
    sem_for i (w :: ws) s1 c (lc :: lw) s3

with sem_call : mem -> funname -> seq value -> leak_fun -> mem -> seq value -> Prop :=
| EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem s1 f.(f_body) lc (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    sem_call m1 fn vargs' (fn, lc) m2 vres'.

(* -------------------------------------------------------------------- *)
(* The generated scheme is borring to use *)
(*
Scheme sem_Ind    := Induction for sem      Sort Prop
with sem_i_Ind    := Induction for sem_i    Sort Prop
with sem_I_Ind    := Induction for sem_I    Sort Prop
with sem_for_Ind  := Induction for sem_for  Sort Prop
with sem_call_Ind := Induction for sem_call Sort Prop.
*)

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> leak_c -> estate -> Prop)
    (Pi_r : estate -> instr_r -> leak_i -> estate -> Prop)
    (Pi : estate -> instr -> leak_i -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> leak_for -> estate -> Prop)
    (Pfun : mem -> funname -> seq value -> leak_fun -> mem -> seq value -> Prop).

  Definition sem_Ind_nil : Prop :=
    forall s : estate, Pc s [::] [::] s.

  Definition sem_Ind_cons : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd) (li : leak_i) (lc : leak_c),
      sem_I s1 i li s2 -> Pi s1 i li s2 -> sem s2 c lc s3 -> Pc s2 c lc s3 -> Pc s1 (i :: c) (li :: lc) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate) (li : leak_i),
      sem_i s1 i li s2 -> Pi_r s1 i li s2 -> Pi s1 (MkI ii i) li s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v' (le lw : leak_e),
      sem_pexpr gd s1 e = ok (v, le) ->
      truncate_val ty v = ok v' →
      write_lval gd x v' s1 = Ok error (s2, lw) ->
      Pi_r s1 (Cassgn x tag ty e) (Lopn (LSub ([:: le ; lw]))) s2.

  Definition sem_Ind_opn : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs) (lo : leak_e),
      sem_sopn gd o s1 xs es = Ok error (s2, lo) ->
      Pi_r s1 (Copn xs t o es) (Lopn lo) s2.

  Definition sem_Ind_if_true : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e) (lc : leak_c),
      sem_pexpr gd s1 e = ok (Vbool true, le) ->
      sem s1 c1 lc s2 -> Pc s1 c1 lc s2 -> Pi_r s1 (Cif e c1 c2) (Lcond le true lc) s2.

  Definition sem_Ind_if_false : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e) (lc : leak_c),
      sem_pexpr gd s1 e = ok (Vbool false, le) ->
      sem s1 c2 lc s2 -> Pc s1 c2 lc s2 -> Pi_r s1 (Cif e c1 c2) (Lcond le false lc) s2.

  Definition sem_Ind_while_true : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : leak_c) 
           (le : leak_e) (lc' : leak_c) (li : leak_i),
      sem s1 c lc s2 -> Pc s1 c lc s2 ->
      sem_pexpr gd s2 e = ok (Vbool true, le) ->
      sem s2 c' lc' s3 -> Pc s2 c' lc' s3 ->
      sem_i s3 (Cwhile a c e c') li s4 -> 
      Pi_r s3 (Cwhile a c e c') li s4 -> 
      Pi_r s1 (Cwhile a c e c') (Lwhile_true lc le lc' li) s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : leak_c) (le : leak_e),
      sem s1 c lc s2 -> Pc s1 c lc s2 ->
      sem_pexpr gd s2 e = ok (Vbool false, le) ->
      Pi_r s1 (Cwhile a c e c') (Lwhile_false lc le) s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_for : Prop :=
    forall (s1 s2 : estate) (i : var_i) r wr (c : cmd) (lr : leak_e) (lf: leak_for),
      sem_range s1 r = ok (wr, lr) ->
      sem_for i wr s1 c lf s2 ->
      Pfor i wr s1 c lf s2 -> Pi_r s1 (Cfor i r c) (Lfor lr lf) s2.

  Definition sem_Ind_for_nil : Prop :=
    forall (s : estate) (i : var_i) (c : cmd),
      Pfor i [::] s c [::] s.

  Definition sem_Ind_for_cons : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i) (w : Z) (ws : seq Z) (c : cmd) (lc : leak_c) (lf : leak_for),
      write_var i w s1 = Ok error s1' ->
      sem s1' c lc s2 -> Pc s1' c lc s2 ->
      sem_for i ws s2 c lf s3 -> Pfor i ws s2 c lf s3 -> Pfor i (w :: ws) s1 c (lc :: lf) s3.

  Hypotheses
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .

  Definition sem_Ind_call : Prop :=
    forall (s1 : estate) (m2 : mem) (s2 : estate)
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs : seq (value * leak_e)) (vs : seq value) (lf : leak_fun) (lw : seq leak_e),
      sem_pexprs gd s1 args = Ok error vargs ->
      sem_call (emem s1) fn (unzip1 vargs) lf m2 vs -> Pfun (emem s1) fn (unzip1 vargs) lf m2 vs ->
      write_lvals gd {| emem := m2; evm := evm s1 |} xs vs = Ok error (s2, lw) ->
      Pi_r s1 (Ccall ii xs fn args) (Lcall (LSub (unzip2 vargs)) lf (LSub lw)) s2.

  Definition sem_Ind_proc : Prop :=
    forall (m1 m2 : mem) (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s1 : estate) (vm2 : vmap) (vres vres': seq value) (lc : leak_c),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      Pc s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun m1 fn vargs' (fn, lc) m2 vres'.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

  Fixpoint sem_Ind (e : estate) (l : cmd) (le : leak_c) (e0 : estate) (s : sem e l le e0) {struct s} :
    Pc e l le e0 :=
    match s in (sem e1 l0 l1 e2) return (Pc e1 l0 l1 e2) with
    | Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c li lc s0 s4 =>
        @Hcons s1 s2 s3 i c li lc s0 (@sem_I_Ind s1 i li s2 s0) s4 (@sem_Ind s2 c lc s3 s4) 
    end

  with sem_i_Ind (e : estate) (i : instr_r) (li : leak_i) (e0 : estate) (s : sem_i e i li e0) {struct s} :
    Pi_r e i li e0 :=
    match s in (sem_i e1 i0 le1 e2) return (Pi_r e1 i0 le1 e2) with
    | @Eassgn s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3 => @Hasgn s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3
    | @Eopn s1 s2 t o xs es lo e1 => @Hopn s1 s2 t o xs es lo e1
    | @Eif_true s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind s1 c1 lc s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind s1 c2 lc s2 s0)
    | @Ewhile_true s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 h2 h3 h4 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 (@sem_Ind s1 c lc s2 h1) h2 h3 (@sem_Ind s2 c' lc' s3 h3) 
          h4 (@sem_i_Ind s3 (Cwhile a c e1 c') lw s4 h4)
    | @Ewhile_false s1 s2 a c e1 c' lc le s0 e2 =>
      @Hwhile_false s1 s2 a c e1 c' lc le s0 (@sem_Ind s1 c lc s2 s0) e2
    | @Efor s1 s2 i0 r c wr lr lf s0 sf =>
      @Hfor s1 s2 i0 r wr c lr lf s0 sf
        (@sem_for_Ind i0 wr s1 c lf s2 sf)
    | @Ecall s1 m2 s2 ii xs f13 args vargs vs lf l2 e2 s0 e3 =>
      @Hcall s1 m2 s2 ii xs f13 args vargs vs lf l2 e2 s0
        (@sem_call_Ind (emem s1) f13 (unzip1 vargs) m2 vs lf s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (li : leak_i) (e0 : estate) (s : sem_I e i li e0) {struct s} :
    Pi e i li e0 :=
    match s in (sem_I e1 i0 le e2) return (Pi e1 i0 le e2) with
    | @EmkI ii i0 s1 s2 li s0 => @HmkI ii i0 s1 s2 li s0 (@sem_i_Ind s1 i0 li s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (lf : leak_for) (e0 : estate)
         (s : sem_for v l e l0 lf e0) {struct s} : Pfor v l e l0 lf e0 :=
    match s in (sem_for v0 l1 e1 l2 le e2) return (Pfor v0 l1 e1 l2 le e2) with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c lc lw e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c lc lw e1 s0 (@sem_Ind s1' c lc s2 s0)
         s4 (@sem_for_Ind i ws s2 c lw s3 s4)
    end

  with sem_call_Ind (m : mem) (f13 : funname) (l : seq value) (m0 : mem)
         (l0 : seq value) (lf : leak_fun) (s : sem_call m f13 l lf m0 l0) {struct s} : Pfun m f13 l lf m0 l0 :=
    match s with
    | @EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem Hvres Hctout =>
       @Hproc m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem (sem_Ind Hsem) Hvres Hctout
    end.

End SEM_IND.

Lemma of_val_undef t t':
  of_val t (Vundef t') =
    Error (if subtype t t' then ErrAddrUndef else ErrType).
Proof.
  by case: t t' => //= [  [] |  [] | p| s []] // [].
Qed.

Lemma of_val_undef_ok t t' v:
  of_val t (Vundef t') <> ok v.
Proof. by rewrite of_val_undef. Qed.

Lemma of_varr t n (a:WArray.array n) z :
  of_val t (Varr a) = ok z -> subtype t (sarr n).
Proof.
  by case: t z => //= n' z; rewrite /WArray.cast; case: ifP.
Qed.

Lemma of_vword t s (w: word s) z :
  of_val t (Vword w) = ok z -> exists s', (s' <= s)%CMP /\ t = sword s'.
Proof.
  case: t z => //= s' w'.
  exists s';split => //=.
  by move: H; rewrite /truncate_word;  case: (s' <= s)%CMP => //=.
Qed.

Lemma of_vint t n z :
  of_val t (Vint n) = ok z -> t = sint.
Proof.
  case: t z => //= s' w'.
Qed.

Definition sem_call_noleak f mem va mem' vr :=
 exists l, sem_call f mem va l mem' vr.

End SEM.
