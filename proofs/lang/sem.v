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

(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Psatz.
Require Export expr memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Module FArray.

  Definition array (T:Type) := Z -> T.

  Definition cnst {T} (t:T) : array T := fun i => t.

  Definition get {T} (a:array T) (i:Z) := a i.

  Definition set {T} (a:array T) (i:Z) (v:T) :=
    fun j => if i == j  then v else a j.

  Lemma setP {T} (a:array T) (w1 w2:Z) (t:T):
    get (set a w1 t) w2 = if w1 == w2 then t else get a w2.
  Proof. done. Qed.

  Lemma setP_eq {T} (a:array T) w (t:T):
    get (set a w t) w = t.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} (a:array T) w1 w2 (t:T):
    w1 != w2 -> get (set a w1 t) w2 = get a w2.
  Proof. by rewrite setP=> /negPf ->. Qed.

  (* FIXME *)
  Axiom eq_ext : forall T (t1 t2:array T), (forall x, get t1 x = get t2 x) -> t1 = t2.

End FArray.

Module Array.

  Definition array (s:positive) T := FArray.array (exec T).

  Definition empty {T:Type} (s:positive) : array s T := FArray.cnst (Error ErrAddrUndef).

  Definition make {T:Type} (s:positive) (t:T) : array s T :=  FArray.cnst (ok t).

  Definition get {T} {s} (a:array s T) w : result error T :=
    if ((0 <=? w) && (w <? Zpos s))%Z then FArray.get a w
    else Error ErrOob.

  Definition set {T} s (a:array s T) x (v:T) : result error (array s T):=
    if ((0 <=? x) && (x <? Zpos s))%Z then ok (FArray.set a x (ok v))
    else Error ErrOob.

  Lemma getP_inv T s (a:array s T) x t:
    get a x = ok t -> ((0 <=? x) && (x <? Zpos s))%Z.
  Proof. by rewrite /get;case: ifP. Qed.

  Lemma getP_empty T s x w: get (@empty T s) x <> ok w.
  Proof. by rewrite /get/empty;case:ifP. Qed.

  Lemma setP_inv T s (a:array s T) x v t:
    set a x v = ok t ->
    0 <= x < Z.pos s.
  Proof.
    rewrite /set.
    case Hind: ((0 <=? x) && (x <? Z.pos s))=> // _.
    move: Hind=> /andP [H1 H2].
    split; [by apply/Z.leb_le|by apply/Z.ltb_lt].
  Qed.

  (* FIXME *)
  Axiom eq_ext : forall T s (t1 t2:array s T), (forall x, get t1 x = get t2 x) -> t1 = t2.

End Array.

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool  => bool
  | sint   => Z
  | sarr n => Array.array n word
  | sword  => word
  end.

(* ** Default values
 * -------------------------------------------------------------------- *)

Definition dflt_val (t : stype) : sem_t t :=
  match t with
  | sbool         => false
  | sint          => Z0
  | sarr n        => @Array.empty word n
  | sword         => I64.repr Z0
  end.

Definition rdflt_ (t : stype) e (r : result e (sem_t t)) : sem_t t :=
  rdflt (dflt_val t) r.

(* ** Values
  * -------------------------------------------------------------------- *)

Inductive value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall n, Array.array n word -> value
  | Vword  :> word -> value
  | Vundef : stype -> value.

Definition undef_b := Vundef sbool.

Definition values := seq value.

Definition undef_error {t} := @Error error t ErrAddrUndef.

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

Definition to_arr n v : exec (Array.array n word) :=
  match v with
  | Varr n' t =>
    match CEDecStype.pos_dec n' n with
    | left H =>
      ok (eq_rect n' (fun p => Array.array p word) t n H)
    | _      => type_error
    end
  | Vundef (sarr n') => if n == n' then undef_error else type_error
  | _                => type_error
  end.

Definition to_word v :=
  match v with
  | Vword w      => ok w
  | Vundef sword => undef_error
  | _            => type_error
  end.

Definition type_of_val (v:value) :=
  match v with
  | Vbool _    => sbool
  | Vint  _    => sint
  | Varr  n _  => sarr n
  | Vword _    => sword
  | Vundef t   => t
  end.

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool  => to_bool
  | sint   => to_int
  | sarr n => to_arr n
  | sword  => to_word
  end.

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | sbool  => Vbool
  | sint   => Vint
  | sarr n => @Varr n
  | sword  => Vword
  end.

Lemma of_val_to_val vt (v: sem_t vt): of_val vt (to_val v) = ok v.
Proof.
  elim: vt v=> // n v /=.
  have ->: CEDecStype.pos_dec n n = left (erefl n).
    by elim: n {v}=> // p0 /= ->.
  by [].
Qed.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t (fun t => exec (sem_t t))).

Definition undef_addr t :=
  match t return exec (sem_t t) with
  | sbool | sint | sword => undef_error
  | sarr n => ok (Array.empty n)
  end.

Definition vmap0  :=
  @Fv.empty (fun t => exec (sem_t t)) (fun x => undef_addr x.(vtype)).

Definition on_vu t r (fv: t -> r) (fu:exec r) (v:exec t) : exec r :=
  match v with
  | Ok v => ok (fv v)
  | Error ErrAddrUndef => fu
  | Error e            => Error e
  end.

Lemma on_vuP T R (fv: T -> R) (fu: exec R) (v:exec T) r P:
  (forall t, v = ok t -> fv t = r -> P) ->
  (v = Error ErrAddrUndef -> fu = ok r -> P) ->
  on_vu fv fu v = ok r -> P.
Proof. by case: v => [a | []] Hfv Hfu //= [];[apply: Hfv | apply Hfu]. Qed.

Definition get_var (m:vmap) x :=
  on_vu (@to_val (vtype x)) (ok (Vundef (vtype x))) (m.[x]%vmap).

(* We do not allows to assign to a variable of type word an undef value *)
Definition set_var (m:vmap) x v : exec vmap :=
  on_vu (fun v => m.[x<-ok v]%vmap)
        (if x.(vtype) == sword then type_error
         else ok m.[x<-undef_addr x.(vtype)]%vmap)
        (of_val (vtype x) v).

Lemma set_varP (m m':vmap) x v P :
   (forall t, of_val (vtype x) v = ok t -> m.[x <- ok t]%vmap = m' -> P) ->
   ( x.(vtype) != sword ->
     of_val (vtype x) v = Error ErrAddrUndef ->
     m.[x<-undef_addr x.(vtype)]%vmap = m' -> P) ->
   set_var m x v = ok m' -> P.
Proof.
  move=> H1 H2;apply on_vuP => //.
  case:ifPn => //.
  by move=> neq /(H2 neq) H [].
Qed.

Definition apply_undef t (v : exec (sem_t t)) :=
  match v with
  | Error ErrAddrUndef => undef_addr t
  | _                  => v
  end.

Definition is_full_array v :=
  match v with
  | Vundef _ => False
  | Varr n t =>
    forall p, (0 <= p < Zpos n)%Z -> exists w, Array.get t p = ok w
  | _ => True
  end.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition lprod ts tr :=
  foldr (fun t tr => t -> tr) tr ts.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Definition mk_sem_sop1 t1 tr (o:sem_t t1 -> sem_t tr) v1 :=
  Let v1 := of_val t1 v1 in
  ok (@to_val tr (o v1)).

Definition mk_sem_sop2 t1 t2 tr (o:sem_t t1 -> sem_t t2 -> sem_t tr) v1 v2 :=
  Let v1 := of_val t1 v1 in
  Let v2 := of_val t2 v2 in
  ok (@to_val tr (o v1 v2)).

Definition sem_op1_b  := @mk_sem_sop1 sbool sbool.
Definition sem_op1_w  := @mk_sem_sop1 sword sword.

Definition sem_op2_b  := @mk_sem_sop2 sbool sbool sbool.
Definition sem_op2_i  := @mk_sem_sop2 sint  sint  sint.
Definition sem_op2_w  := @mk_sem_sop2 sword sword sword.
Definition sem_op2_ib := @mk_sem_sop2 sint  sint  sbool.
Definition sem_op2_wb := @mk_sem_sop2 sword sword sbool.

Definition sem_lsr (v i:word) :=
  let i := I64.and i x86_shift_mask in
  if i == I64.zero then v else I64.shru v i.

Definition sem_lsl (v i:word) :=
  let i := I64.and i x86_shift_mask in
  if i == I64.zero then v else I64.shl v i.

Definition sem_asr (v i:word) :=
  let i := I64.and i x86_shift_mask in
  if i == I64.zero then v else I64.shr v i.

Definition sem_sop1 (o:sop1) :=
  match o with
  | Onot   => sem_op1_b negb
  | Olnot  => sem_op1_w I64.not
  end.

Definition sem_sop2 (o:sop2) :=
  match o with
  | Oand => sem_op2_b andb
  | Oor  => sem_op2_b orb

  | Oadd Op_int  => sem_op2_i Z.add
  | Oadd Op_w    => sem_op2_w I64.add
  | Omul Op_int  => sem_op2_i Z.mul
  | Omul Op_w    => sem_op2_w I64.mul
  | Osub Op_int  => sem_op2_i Z.sub
  | Osub Op_w    => sem_op2_w I64.sub

  | Oland        => sem_op2_w I64.and
  | Olor         => sem_op2_w I64.or
  | Olxor        => sem_op2_w I64.xor
  | Olsr         => sem_op2_w sem_lsr
  | Olsl         => sem_op2_w sem_lsl
  | Oasr         => sem_op2_w sem_asr

  | Oeq Cmp_int  => sem_op2_ib Z.eqb
  | Oeq _        => sem_op2_wb weq
  | Oneq Cmp_int => sem_op2_ib (fun x y => negb (Z.eqb x y))
  | Oneq _       => sem_op2_wb (fun x y => negb (weq x y))
  | Olt Cmp_int  => sem_op2_ib Z.ltb
  | Ole Cmp_int  => sem_op2_ib Z.leb
  | Ogt Cmp_int  => sem_op2_ib Z.gtb
  | Oge Cmp_int  => sem_op2_ib Z.geb
  | Olt Cmp_sw   => sem_op2_wb wslt
  | Ole Cmp_sw   => sem_op2_wb wsle
  | Ogt Cmp_sw   => sem_op2_wb (fun x y => wslt y x)
  | Oge Cmp_sw   => sem_op2_wb (fun x y => wsle y x)
  | Olt Cmp_uw   => sem_op2_wb wult
  | Ole Cmp_uw   => sem_op2_wb wule
  | Ogt Cmp_uw   => sem_op2_wb (fun x y => wult y x)
  | Oge Cmp_uw   => sem_op2_wb (fun x y => wule y x)
  end.

Import Memory.

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition on_arr_var A (s:estate) (x:var) (f:forall n, Array.array n word -> exec A) :=
  Let v := get_var s.(evm) x in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

Notation "'Let' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@on_arr_var _ s x (fun n (t:Array.array n word) => body)) (at level 25, s at level 0).

Lemma on_arr_varP A (f : forall n : positive, Array.array n word -> exec A) v s x P:
  (forall n t, vtype x = sarr n ->
               get_var (evm s) x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var s x f = ok v -> P.
Proof.
  rewrite /on_arr_var=> H;apply: rbindP => vx.
  case: x H => -[ | | n | ] nx;rewrite /get_var => H;
    case Heq : ((evm s).[_])%vmap => [v' | e] //=.
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]; apply: H => //;rewrite Heq. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
Qed.

Definition Varr_inj n n' t t' : @Varr n t = @Varr n' t' -> n = n' /\ t = t' :=
  fun e => let 'Logic.eq_refl := e in conj Logic.eq_refl Logic.eq_refl.

Lemma Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
Proof. by move=> /Varr_inj []. Qed.

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Pcast e  =>
    Let z := sem_pexpr s e >>= to_int in
    ok (Vword (I64.repr z))
  | Pvar v => get_var s.(evm) v
  | Pget x e =>
      Let (n,t) := s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := Array.get t i in
      ok (Vword w)
  | Pload x e =>
    Let w1 := get_var s.(evm) x >>= to_word in
    Let w2 := sem_pexpr s e >>= to_word in
    Let w  := read_mem s.(emem) (I64.add w1 w2) in
    ok (@to_val sword w)
  | Papp1 o e1 =>
    Let v1 := sem_pexpr s e1 in
    sem_sop1 o v1
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    sem_sop2 o v1 v2
  | Pif e e1 e2 =>
    Let b := sem_pexpr s e >>= to_bool in
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    if (type_of_val v1 == type_of_val v2) then
      ok (if b then v1 else v2)
    else
      type_error
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok ({| emem := s.(emem); evm := vm |}).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s:estate) ty v :=
  on_vu (fun v => s) (if ty == sword then type_error else ok s)
          (of_val ty v).

Definition write_lval (l:lval) (v:value) (s:estate) : exec estate :=
  match l with
  | Lnone _ ty => write_none s ty v
  | Lvar x => write_var x v s
  | Lmem x e =>
    Let vx := get_var (evm s) x >>= to_word in
    Let ve := sem_pexpr s e >>= to_word in
    let p := wadd vx ve in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word v in
    Let m :=  write_mem s.(emem) p w in
    ok {|emem := m;  evm := s.(evm) |}
  | Laset x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word v in
    Let t := Array.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |})
  end.

Definition write_lvals (s:estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

Fixpoint app_sopn ts : sem_prod ts (exec values) -> values -> exec values :=
  match ts return sem_prod ts (exec values) -> values -> exec values with
  | [::] => fun (o:exec values) (vs:values) =>
    match vs with
    | [::] => o
    | _    => type_error
    end
  | t::ts => fun (o:sem_t t -> sem_prod ts (exec values)) (vs:values) =>
    match vs with
    | [::]  => type_error
    | v::vs =>
      Let v := of_val t v in
      app_sopn (o v) vs
    end
  end.
Arguments app_sopn ts o l:clear implicits.

Definition pval t1 t2 (p: sem_t t1 * sem_t t2) :=
  [::to_val p.1; to_val p.2].

Definition SF_of_word (w : word) :=
  msb w.

Definition PF_of_word (w : word) :=
  lsb w.

Definition ZF_of_word (w : word) :=
  I64.eq w I64.zero.

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_bwop (w : word) :=
  (*  OF   ; CF   ; SF          ; PF          ; ZF          ] *)
  [:: false; false; SF_of_word w; PF_of_word w; ZF_of_word w].

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_aluop (w : word) (vu vs : Z) :=
  (*  OF                  ; CF                    *)
  [:: I64.signed   w != vs; I64.unsigned w != vu;
  (*  SF          ; PF          ; ZF          ] *)
      SF_of_word w; PF_of_word w; ZF_of_word w ].

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_mul (ov : bool) :=
  (*  OF      ; CF                    *)
  [:: Vbool ov;  Vbool ov;
  (*  SF      ; PF       ; ZF         *)
     undef_b  ; undef_b   ; undef_b ].

(* -------------------------------------------------------------------- *)

Definition rflags_of_div :=
  (*  OF      ; CF                    *)
  [:: undef_b  ; undef_b  ;
  (*  SF      ; PF       ; ZF         *)
      undef_b  ; undef_b   ; undef_b ].

(* -------------------------------------------------------------------- *)
(*  OF; SF; PF; ZF  *)
Definition rflags_of_aluop_nocf (w : word) (vs : Z) :=
  (*  OF                  *)
  [:: I64.signed   w != vs;
  (*  SF          ; PF          ; ZF          ] *)
      SF_of_word w; PF_of_word w; ZF_of_word w ].

Definition flags_w (bs:seq bool) (w:word) : exec values :=
  ok ((map Vbool bs) ++ [:: Vword w]).

Definition rflags_of_aluop_w (w : word) (vu vs : Z) : exec values :=
  flags_w (rflags_of_aluop w vu vs) w.

Definition rflags_of_aluop_nocf_w (w : word) (vs : Z) : exec values :=
  flags_w (rflags_of_aluop_nocf w vs) w.

Definition rflags_of_bwop_w (w : word) : exec values :=
  flags_w (rflags_of_bwop w) w.

Definition vbools bs : exec values := ok (List.map Vbool bs).

(* -------------------------------------------------------------------- *)
Definition x86_MOV (x:word) : exec values :=
  ok [:: Vword x].

Definition x86_CMOVcc (b:bool) (x y:word) : exec values :=
  ok [:: Vword (if b then x else y)].

Definition x86_add (v1 v2 : word) :=
  rflags_of_aluop_w
    (I64.add v1 v2)
    (I64.unsigned v1 + I64.unsigned v2)%Z
    (I64.signed   v1 + I64.signed   v2)%Z.

Definition x86_sub (v1 v2 : word) :=
  rflags_of_aluop_w
    (I64.sub v1 v2)
    (I64.unsigned v1 - I64.unsigned v2)%Z
    (I64.signed   v1 - I64.signed   v2)%Z.

Definition x86_mul (v1 v2:word): exec values :=
  let lo := I64.mul v1 v2 in
  let hi := I64.mulhu v1 v2 in
  let ov := dwordu hi lo in
  let ov := (ov >? I64.max_unsigned)%Z in
  ok (rflags_of_mul ov ++ [::Vword hi; Vword lo]).

Definition x86_imul (v1 v2:word) : exec values:=
  let lo := I64.mul v1 v2 in
  let hi := I64.mulhs v1 v2 in
  let ov := dwords hi lo in
  let ov := (ov <? I64.min_signed)%Z || (ov >? I64.max_unsigned)%Z in
  ok (rflags_of_mul ov ++ [::Vword hi; Vword lo]).

Definition x86_imul64 (v1 v2:word) : exec values:=
  let lo := I64.mul v1 v2 in
  let hi := I64.mulhs v1 v2 in
  let ov := dwords hi lo in
  let ov := (ov <? I64.min_signed)%Z || (ov >? I64.max_unsigned)%Z in
  ok (rflags_of_mul ov ++ [::Vword lo]).

Definition x86_div (hi lo dv:word) : exec values:=
  let dd := dwordu hi lo in
  let dv := I64.unsigned dv in
  let q  := (dd  /  dv)%Z in
  let r  := (dd mod dv)%Z in
  let ov := (q >? I64.max_unsigned)%Z in

  if (dv == 0)%Z || ov then type_error else

  ok (rflags_of_div ++ [:: Vword (I64.repr q); Vword (I64.repr r)]).

Definition x86_idiv (hi lo dv:word) : exec values :=
  let dd := dwords hi lo in
  let dv := I64.signed dv in
  let q  := (Z.quot dd dv)%Z in
  let r  := (Z.rem  dd dv)%Z in
  let ov := (q <? I64.min_signed)%Z || (q >? I64.max_signed)%Z in

  if (dv == 0)%Z || ov then type_error else

  ok (rflags_of_div ++ [:: Vword (I64.repr q); Vword (I64.repr r)]).

Definition x86_adc (v1 v2 : word) (c:bool) :=
  let c := b_to_w c in
  rflags_of_aluop_w
    (I64.add_carry v1 v2 c)
    (I64.unsigned v1 + I64.unsigned v2 + c)%Z
    (I64.signed   v1 + I64.signed   v2 + c)%Z.

Definition x86_sbb (v1 v2 : word) (c:bool) :=
  let c := b_to_w c in
  rflags_of_aluop_w
    (I64.sub_borrow v1 v2 c)
    (I64.unsigned v1 - (I64.unsigned v2 + c))%Z
    (I64.signed   v1 - (I64.signed   v2 + c))%Z.

Definition x86_inc (w:word) :=
  rflags_of_aluop_nocf_w
    (I64.add w I64.one)
    (I64.signed w + 1)%Z.

Definition x86_dec (w:word) :=
  rflags_of_aluop_nocf_w
    (I64.sub w I64.one)
    (I64.signed w - 1)%Z.

Definition x86_setcc (b:bool) : exec values := ok [:: Vword (b_to_w b)].

Definition check_scale (s:Z) :=
  (s == 1%Z) || (s == 2%Z) || (s == 4%Z) || (s == 8%Z).

Definition x86_lea (disp base:word) (scale:word) (offset:word) : exec values :=
  if check_scale scale then
    ok [::Vword (I64.add disp (I64.add base (I64.mul (I64.repr scale) offset)))]
  else type_error.

Definition x86_test (x y: word) : exec values :=
  vbools (rflags_of_bwop (I64.and x y)).

Definition x86_cmp (x y: word) :=
  vbools
    (rflags_of_aluop (I64.sub x y)
       (I64.unsigned x - I64.unsigned y)%Z (I64.signed x - I64.signed y)%Z).

Definition x86_and (v1 v2: word) :=
  rflags_of_bwop_w
    (I64.and v1 v2).

Definition x86_or (v1 v2: word) :=
  rflags_of_bwop_w
    (I64.or v1 v2).

Definition x86_xor (v1 v2: word) :=
  rflags_of_bwop_w
    (I64.xor v1 v2).

Definition x86_not (v:word) : exec values:=
  ok [:: Vword (I64.not v)].

Definition x86_shl (v i: word) : exec values :=
  let i := I64.and i x86_shift_mask in
  if i == I64.zero then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := msb (I64.shl v (I64.sub i I64.one)) in
    let r  := I64.shl v i in
    let OF :=
      if i == I64.one then Vbool (msb r (+) rc)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_shr (v i: word) : exec values :=
  let i := I64.and i x86_shift_mask in
  if i == I64.zero then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := lsb (I64.shru v (I64.sub i I64.one)) in
    let r  := I64.shru v i in

    let OF :=
      if i == I64.one then Vbool (msb r)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_sar (v i: word) : exec values :=
  let i := I64.and i x86_shift_mask in
  if i == I64.zero then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := lsb (I64.shr v (I64.sub i I64.one)) in
    let r  := I64.shr v i in

    let OF :=
      if i == I64.one then Vbool false
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Notation app_b   o := (app_sopn [:: sbool] o).
Notation app_w   o := (app_sopn [:: sword] o).
Notation app_ww  o := (app_sopn [:: sword; sword] o).
Notation app_www o := (app_sopn [:: sword; sword; sword] o).
Notation app_wwb o := (app_sopn [:: sword; sword; sbool] o).
Notation app_bww o := (app_sopn [:: sbool; sword; sword] o).
Notation app_w4 o  := (app_sopn [:: sword; sword; sword; sword] o).

Definition sem_sopn (o:sopn) :  values -> exec values :=
  match o with
  | Omulu        => app_ww  (fun x y => ok (@pval sword sword (wumul x y)))
  | Oaddcarry    => app_wwb (fun x y c => ok (@pval sbool sword (waddcarry x y c)))
  | Osubcarry    => app_wwb (fun x y c => ok (@pval sbool sword (wsubcarry x y c)))

  (* Low level x86 operations *)
  | Ox86_MOV	 => app_w    x86_MOV
  | Ox86_CMOVcc  => (fun v => match v with
    | [:: v1; v2; v3] =>
      Let b := to_bool v1 in
      if b then
        Let w2 := to_word v2 in ok [:: Vword w2]
      else
        Let w3 := to_word v3 in ok [:: Vword w3]
    | _ => type_error end)
  | Ox86_ADD     => app_ww   x86_add
  | Ox86_SUB     => app_ww   x86_sub
  | Ox86_MUL     => app_ww   x86_mul
  | Ox86_IMUL    => app_ww   x86_imul
  | Ox86_IMUL64    => app_ww   x86_imul64
  | Ox86_DIV     => app_www  x86_div
  | Ox86_IDIV    => app_www  x86_idiv
  | Ox86_ADC     => app_wwb  x86_adc
  | Ox86_SBB     => app_wwb  x86_sbb
  | Ox86_INC     => app_w    x86_inc
  | Ox86_DEC     => app_w    x86_dec
  | Ox86_SETcc   => app_b    x86_setcc
  | Ox86_LEA     => app_w4   x86_lea
  | Ox86_TEST    => app_ww   x86_test
  | Ox86_CMP     => app_ww   x86_cmp
  | Ox86_AND     => app_ww   x86_and
  | Ox86_OR      => app_ww   x86_or
  | Ox86_XOR     => app_ww   x86_xor
  | Ox86_NOT     => app_w    x86_not
  | Ox86_SHL     => app_ww x86_shl
  | Ox86_SHR     => app_ww x86_shr
  | Ox86_SAR     => app_ww x86_sar
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM.

Variable P:prog.

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let i1 := sem_pexpr s pe1 >>= to_int in
  Let i2 := sem_pexpr s pe2 >>= to_int in
  ok (wrange d i1 i2).

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_I : estate -> instr -> estate -> Prop :=
| EmkI ii i s1 s2:
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

with sem_i : estate -> instr_r -> estate -> Prop :=
| Eassgn s1 s2 (x:lval) tag e:
    (Let v := sem_pexpr s1 e in write_lval x v s1) = ok s2 ->
    sem_i s1 (Cassgn x tag e) s2

| Eopn s1 s2 o xs es:
    sem_pexprs s1 es >>= sem_sopn o >>= (write_lvals s1 xs) = ok s2 ->
    sem_i s1 (Copn xs o es) s2

| Eif_true s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok true ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok false ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 s4 c e c' :
    sem s1 c s2 ->
    sem_pexpr s2 e >>= to_bool = ok true ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile c e c') s4 ->
    sem_i s1 (Cwhile c e c') s4

| Ewhile_false s1 s2 c e c' :
    sem s1 c s2 ->
    sem_pexpr s2 e >>= to_bool = ok false ->
    sem_i s1 (Cwhile c e c') s2

| Efor s1 s2 (i:var_i) d lo hi c vlo vhi :
    sem_pexpr s1 lo >>= to_int = ok vlo ->
    sem_pexpr s1 hi >>= to_int = ok vhi ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    sem_i s1 (Cfor i (d, lo, hi) c) s2

| Ecall s1 m2 s2 ii xs f args vargs vs :
    sem_pexprs s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_lvals {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
    write_var i (Vint w) s1 = ok s1' ->
    sem s1' c s2 ->
    sem_for i ws s2 c s3 ->
    sem_for i (w :: ws) s1 c s3

with sem_call : mem -> funname -> seq value -> mem -> seq value -> Prop :=
| EcallRun m1 m2 fn f vargs s1 vm2 vres:
    get_fundef P fn = Some f ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem s1 f.(f_body) (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    List.Forall is_full_array vres ->
    sem_call m1 fn vargs m2 vres.

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
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi : estate -> instr -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : mem -> funname -> seq value -> mem -> seq value -> Prop).

  Hypothesis Hnil : forall s : estate, Pc s [::] s.

  Hypothesis Hcons : forall (s1 s2 s3 : estate) (i : instr) (c : cmd),
    sem_I s1 i s2 -> Pi s1 i s2 -> sem s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.

  Hypothesis HmkI : forall (ii : instr_info) (i : instr_r) (s1 s2 : estate),
    sem_i s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

  Hypothesis Hasgn : forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) (e : pexpr),
    Let v := sem_pexpr s1 e in write_lval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.

  Hypothesis Hopn : forall (s1 s2 : estate) (o : sopn) (xs : lvals) (es : pexprs),
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x in write_lvals s1 xs x = Ok error s2 ->
    Pi_r s1 (Copn xs o es) s2.

  Hypothesis Hif_true : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Hypothesis Hif_false : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Hypothesis Hwhile_true : forall (s1 s2 s3 s4 : estate) (c : cmd) (e : pexpr) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = Ok error true ->
    sem s2 c' s3 -> Pc s2 c' s3 ->
    sem_i s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.

  Hypothesis Hwhile_false : forall (s1 s2 : estate) (c : cmd) (e : pexpr) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = Ok error false ->
    Pi_r s1 (Cwhile c e c') s2.

  Hypothesis Hfor : forall (s1 s2 : estate) (i : var_i) (d : dir)
         (lo hi : pexpr) (c : cmd) (vlo vhi : Z),
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

  Hypothesis Hfor_nil : forall (s : estate) (i : var_i) (c : cmd), Pfor i [::] s c s.

  Hypothesis Hfor_cons : forall (s1 s1' s2 s3 : estate) (i : var_i)
         (w : Z) (ws : seq Z) (c : cmd),
    write_var i w s1 = Ok error s1' ->
    sem s1' c s2 -> Pc s1' c s2 ->
    sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypothesis Hcall : forall (s1 : estate) (m2 : mem) (s2 : estate)
         (ii : inline_info) (xs : lvals)
         (fn : funname) (args : pexprs) (vargs vs : seq value),
    sem_pexprs s1 args = Ok error vargs ->
    sem_call (emem s1) fn vargs m2 vs -> Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.

  Hypothesis Hproc : forall (m1 m2 : mem) (fn:funname) (f : fundef) (vargs : seq value)
         (s1 : estate) (vm2 : vmap) (vres : seq value),
    get_fundef P fn = Some f ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    List.Forall is_full_array vres ->
    Pfun m1 fn vargs m2 vres.

  Fixpoint sem_Ind (e : estate) (l : cmd) (e0 : estate) (s : sem e l e0) {struct s} :
    Pc e l e0 :=
    match s in (sem e1 l0 e2) return (Pc e1 l0 e2) with
    | Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c s0 s4 =>
        @Hcons s1 s2 s3 i c s0 (@sem_I_Ind s1 i s2 s0) s4 (@sem_Ind s2 c s3 s4)
    end

  with sem_i_Ind (e : estate) (i : instr_r) (e0 : estate) (s : sem_i e i e0) {struct s} :
    Pi_r e i e0 :=
    match s in (sem_i e1 i0 e2) return (Pi_r e1 i0 e2) with
    | @Eassgn s1 s2 x tag e1 e2 => @Hasgn s1 s2 x tag e1 e2
    | @Eopn s1 s2 o xs es e1 => @Hopn s1 s2 o xs es e1
    | @Eif_true s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c1 s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c2 s2 s0)
    | @Ewhile_true s1 s2 s3 s4 c e1 c' s0 e2 s5 s6 =>
      @Hwhile_true s1 s2 s3 s4 c e1 c' s0 (@sem_Ind s1 c s2 s0) e2 s5 (@sem_Ind s2 c' s3 s5) s6
          (@sem_i_Ind s3 (Cwhile c e1 c') s4 s6)
    | @Ewhile_false s1 s2 c e1 c' s0 e2 =>
      @Hwhile_false s1 s2 c e1 c' s0 (@sem_Ind s1 c s2 s0) e2
    | @Efor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0 =>
      @Hfor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0
        (@sem_for_Ind i0 (wrange d vlo vhi) s1 c s2 s0)
    | @Ecall s1 m2 s2 ii xs f13 args vargs vs e2 s0 e3 =>
      @Hcall s1 m2 s2 ii xs f13 args vargs vs e2 s0
        (@sem_call_Ind (emem s1) f13 vargs m2 vs s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (e0 : estate) (s : sem_I e i e0) {struct s} :
    Pi e i e0 :=
    match s in (sem_I e1 i0 e2) return (Pi e1 i0 e2) with
    | @EmkI ii i0 s1 s2 s0 => @HmkI ii i0 s1 s2 s0 (@sem_i_Ind s1 i0 s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (e0 : estate)
         (s : sem_for v l e l0 e0) {struct s} : Pfor v l e l0 e0 :=
    match s in (sem_for v0 l1 e1 l2 e2) return (Pfor v0 l1 e1 l2 e2) with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c e1 s0 (@sem_Ind s1' c s2 s0)
         s4 (@sem_for_Ind i ws s2 c s3 s4)
    end

  with sem_call_Ind (m : mem) (f13 : funname) (l : seq value) (m0 : mem)
         (l0 : seq value) (s : sem_call m f13 l m0 l0) {struct s} : Pfun m f13 l m0 l0 :=
    match s with
    | @EcallRun m1 m2 fn f vargs s1 vm2 vres Hget Hw Hsem Hmap Hvres =>
       @Hproc m1 m2 fn f vargs s1 vm2 vres Hget Hw Hsem (sem_Ind Hsem) Hmap Hvres
    end.

End SEM_IND.

(* -------------------------------------------------------------------- *)
Lemma size_wrange d z1 z2 :
  size (wrange d z1 z2) = Z.to_nat (z2 - z1).
Proof. by case: d => /=; rewrite ?size_rev size_map size_iota. Qed.

Lemma nth_wrange z0 d z1 z2 n : (n < Z.to_nat (z2 - z1))%nat ->
  nth z0 (wrange d z1 z2) n =
    if   d is UpTo
    then z1 + Z.of_nat n
    else z2 - Z.of_nat n.
Proof.
case: d => ltn /=;
  by rewrite (nth_map 0%nat) ?size_iota ?nth_iota.
Qed.

Lemma last_wrange_up_ne z0 lo hi :
  lo < hi -> last z0 (wrange UpTo lo hi) = hi - 1.
Proof.
move=> lt; rewrite -nth_last nth_wrange; last rewrite size_wrange prednK //.
rewrite size_wrange -subn1 Nat2Z.inj_sub; first by rewrite Z2Nat.id; lia.
+ apply/leP/ltP; rewrite -Z2Nat.inj_0; apply Z2Nat.inj_lt; lia.
+ apply/ltP; rewrite -Z2Nat.inj_0; apply Z2Nat.inj_lt; lia.
Qed.

Lemma last_wrange_up lo hi : last (hi-1) (wrange UpTo lo hi) = hi - 1.
Proof.
case: (Z_lt_le_dec lo hi) => [lt|le]; first by apply: last_wrange_up_ne.
rewrite -nth_last nth_default // size_wrange.
by rewrite [Z.to_nat _](_ : _ = 0%nat) ?Z_to_nat_le0 //; lia.
Qed.

Lemma wrange_cons lo hi : lo < hi ->
  lo - 1 :: wrange UpTo lo hi = wrange UpTo (lo - 1) hi.
Proof.
set s1 := wrange _ _ _; set s2 := wrange _ _ _ => /=.
move=> lt; apply/(@eq_from_nth _ 0) => /=.
+ rewrite {}/s1 {}/s2 !size_wrange -Z2Nat.inj_succ; try lia.
  by apply: Nat2Z.inj; rewrite !Z2Nat.id; lia.
rewrite {1}/s1 size_wrange; case => [|i].
+ rewrite /s2 nth_wrange /=; try lia.
  by rewrite -Z2Nat.inj_0; apply/leP/Z2Nat.inj_lt; lia.
move=> lti; rewrite -[nth _ (_ :: _) _]/(nth 0 s1 i) {}/s1 {}/s2.
rewrite !nth_wrange; first lia; last first.
+ by apply/leP; move/leP: lti; lia.
apply/leP/Nat2Z.inj_lt; rewrite Z2Nat.id; try lia.
move/leP/Nat2Z.inj_lt: lti; try rewrite -Z2Nat.inj_succ; try lia.
by rewrite Z2Nat.id; lia.
Qed.

(* -------------------------------------------------------------------- *)

Lemma sem_app l1 l2 s1 s2 s3:
  sem s1 l1 s2 -> sem s2 l2 s3 ->
  sem s1 (l1 ++ l2) s3.
Proof.
  elim: l1 s1;first by move=> s1 H1;inversion H1.
  move=> a l Hrec s1 H1;inversion H1;subst;clear H1 => /= Hl2.
  by apply (Eseq H3);apply Hrec.
Qed.

Lemma sem_seq1 i s1 s2:
  sem_I s1 i s2 -> sem s1 [::i] s2.
Proof.
  move=> Hi; apply (Eseq Hi);constructor.
Qed.

Definition vmap_eq_except (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vmap_eq_exceptT vm2 s vm1 vm3:
  vm1 = vm2 [\s] -> vm2 = vm3 [\s] -> vm1 = vm3 [\s].
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma vmap_eq_exceptI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 = vm2 [\s1] -> vm1 = vm2 [\s2].
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vmap_eq_exceptS vm1 s vm2 : vm1 = vm2 [\s] -> vm2 = vm1 [\s].
Proof. by move=> Heq x Hin;rewrite Heq. Qed.

Global Instance equiv_vmap_eq_except s: Equivalence (vmap_eq_except s).
Proof.
  constructor=> //.
  move=> ??;apply: vmap_eq_exceptS.
  move=> ???;apply: vmap_eq_exceptT.
Qed.

Global Instance vmap_eq_except_impl :
  Proper (Sv.Subset ==> eq ==> eq ==> Basics.impl) vmap_eq_except.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vmap_eq_exceptI. Qed.

Global Instance vmap_eq_except_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vmap_eq_except.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vmap_eq_exceptI;rewrite Heq. Qed.

Lemma vrvP_var (x:var_i) v s1 s2 :
  write_var x v s1 = ok s2 ->
  s1.(evm) = s2.(evm) [\ Sv.add x Sv.empty].
Proof.
  rewrite /write_var; apply: rbindP => vm.
  by apply: set_varP => [t | _]=> ? <- [<-] z Hz; rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.

Lemma write_noneP s s' ty v:
  write_none s ty v = ok s' ->
  s' = s /\
  ((exists u, of_val ty v = ok u) \/ of_val ty v = Error ErrAddrUndef /\ ty <> sword).
Proof.
  apply: on_vuP => [u ? -> | ?].
  + by split => //;left;exists u.
  by case:ifPn => // /eqP ? [->]; split => //; right.
Qed.

Lemma vrvP (x:lval) v s1 s2 :
  write_lval x v s1 = ok s2 ->
  s1.(evm) = s2.(evm) [\ vrv x].
Proof.
  case x => /= [ _ ty | ? /vrvP_var| y e| y e] //.
  + by move=> /write_noneP [->].
  + by t_rbindP => -[<-].
  apply: on_arr_varP => n t; case:y => -[] ty yn yi /= -> Hy.
  apply: rbindP => we;apply: rbindP => ve He Hve.
  apply: rbindP => v0 Hv0;apply rbindP => t' Ht'.
  rewrite /set_var /=.
  case: CEDecStype.pos_dec => //= H [<-] /=.
  by move=> z Hz;rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.

Lemma vrvsP xs vs s1 s2 :
  write_lvals s1 xs vs = ok s2 ->
  s1.(evm) = s2.(evm) [\ vrvs xs].
Proof.
  elim: xs vs s1 s2 => [|x xs Hrec] [|v vs] s1 s2 //=.
  + by move=> [<-].
  apply: rbindP => s /vrvP Hrv /Hrec Hrvs.
  rewrite vrvs_cons;apply: (@vmap_eq_exceptT (evm s)).
  + by apply: vmap_eq_exceptI Hrv;SvD.fsetdec.
  by apply: vmap_eq_exceptI Hrvs;SvD.fsetdec.
Qed.

Lemma writeP c s1 s2 :
   sem s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c].
Proof.
  apply (@sem_Ind (fun s1 c s2 => s1.(evm) = s2.(evm) [\ write_c c])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_i i])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_I i])
                  (fun x ws s1 c s2 =>
                     s1.(evm) = s2.(evm) [\ (Sv.union (Sv.singleton x) (write_c c))])
                  (fun _ _ _ _ _ => True)) => {c s1 s2} //.
  + move=> s1 s2 s3 i c _ Hi _ Hc z;rewrite write_c_cons => Hnin.
    by rewrite Hi ?Hc //;SvD.fsetdec.
  + move=> s1 s2 x tag e; case: sem_pexpr => //= v Hw z.
    by rewrite write_i_assgn;apply (vrvP Hw).
  + move=> s1 s2 o xs es; case: (Let _ := sem_pexprs _ _ in _) => //= vs Hw z.
    by rewrite write_i_opn;apply (vrvsP Hw).
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 s3 s4 c e c' _ Hc _ _ Hc' _ Hw z Hnin; rewrite Hc ?Hc' ?Hw //;
    move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + move=> s1 s2 c e c' _ Hc _ z Hnin; rewrite Hc //.
    by move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + by move=> s1 s2 i d lo hi c vlo vhi _ _ _ Hrec z;rewrite write_i_for;apply Hrec.
  + move=> s1 s1' s2 s3 i w ws c Hw _ Hc _ Hf z Hnin.
    by rewrite (vrvP_var Hw) ?Hc ?Hf //;SvD.fsetdec.
  + move=> s1 m2 s2 ii xs fn args vargs vs _ _ _ Hw z.
    by rewrite write_i_call;apply (vrvsP Hw).
Qed.

Lemma write_IP i s1 s2 :
   sem_I s1 i s2 -> s1.(evm) = s2.(evm) [\ write_I i].
Proof.
  move=> /sem_seq1 /writeP.
  have := write_c_cons i [::].
  move=> Heq H x Hx;apply H; SvD.fsetdec.
Qed.

Lemma write_iP i s1 s2 :
   sem_i s1 i s2 -> s1.(evm) = s2.(evm) [\ write_i i].
Proof. by move=> /EmkI -/(_ 1%positive) /write_IP. Qed.

Definition eq_on (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Lemma eq_onT s vm1 vm2 vm3:
  vm1 =[s] vm2 -> vm2 =[s] vm3 -> vm1 =[s] vm3.
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma eq_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 =[s2] vm2 -> vm1 =[s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma eq_onS vm1 s vm2 : vm1 =[s] vm2 -> vm2 =[s] vm1.
Proof. by move=> Heq x Hin;rewrite Heq. Qed.

Global Instance equiv_eq_on s: Equivalence (eq_on s).
Proof.
  constructor=> //.
  move=> ??;apply: eq_onS.
  move=> ???;apply: eq_onT.
Qed.

Global Instance eq_on_impl : Proper (Basics.flip Sv.Subset ==> eq ==> eq ==> Basics.impl) eq_on.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: eq_onI. Qed.

Global Instance eq_on_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) eq_on.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: eq_onI;rewrite Heq. Qed.

Lemma disjoint_eq_on s r s1 s2 v:
  disjoint s (vrv r) ->
  write_lval r v s1 = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma disjoint_eq_ons s r s1 s2 v:
  disjoint s (vrvs r) ->
  write_lvals s1 r v = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvsP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma get_var_eq_on s vm' vm v: Sv.In v s -> vm =[s]  vm' -> get_var vm v = get_var vm' v.
Proof. by move=> Hin Hvm;rewrite /get_var Hvm. Qed.

Lemma on_arr_var_eq_on s' X s A x (f:forall n, Array.array n word -> exec A) :
   evm s =[X] evm s' -> Sv.In x X ->
   on_arr_var s x f = on_arr_var s' x f.
Proof.
  by move=> Heq Hin;rewrite /on_arr_var;rewrite (get_var_eq_on Hin Heq).
Qed.

Lemma read_e_eq_on s vm' vm m e:
  vm =[read_e_rec s e] vm'->
  sem_pexpr (Estate m vm) e = sem_pexpr (Estate m vm') e.
Proof.
  elim:e s => //= [e He|v|v e He|v e He|o e He|o e1 He1 e2 He2|e He e1 He1 e2 He2] s.
  + by move=> /He ->.
  + move=> /get_var_eq_on -> //;SvD.fsetdec.
  + move=> Heq;rewrite (He _ Heq)=> {He}.
    rewrite (@on_arr_var_eq_on
      {| emem := m; evm := vm' |} _ {| emem := m; evm := vm |} _ _ _ Heq) ?read_eE //.
    by SvD.fsetdec.
  + by move=> Hvm;rewrite (get_var_eq_on _ Hvm) ?(He _ Hvm) // read_eE;SvD.fsetdec.
  + by move=> /He ->.
  + move=> Heq;rewrite (He1 _ Heq) (He2 s) //.
    by move=> z Hin;apply Heq;rewrite read_eE;SvD.fsetdec.
  move=> Heq; rewrite (He _ Heq) (He1 s) ? (He2 s) //.
  + move=> z Hin;apply Heq;rewrite !read_eE.
    by move: Hin;rewrite read_eE;SvD.fsetdec.
  move=> z Hin;apply Heq;rewrite !read_eE.
  by move: Hin;rewrite read_eE;SvD.fsetdec.
Qed.

Lemma read_es_eq_on es s m vm vm':
  vm =[read_es_rec s es] vm'->
  sem_pexprs (Estate m vm) es = sem_pexprs (Estate m vm') es.
Proof.
  rewrite /sem_pexprs;elim: es s => //= e es Hes s Heq.
  rewrite (@read_e_eq_on s vm').
  + by case:sem_pexpr => //= v;rewrite (Hes (read_e_rec s e)).
  by move=> z Hin;apply Heq;rewrite read_esE;SvD.fsetdec.
Qed.

Lemma set_var_eq_on s x v vm1 vm2 vm1':
  set_var vm1 x v = ok vm2 ->
  vm1 =[s]  vm1' ->
  exists vm2' : vmap,
     vm2 =[Sv.union (Sv.add x Sv.empty) s]  vm2' /\
     set_var vm1' x v = ok vm2'.
Proof.
  (apply: set_varP;rewrite /set_var) => [t | /negbTE ->] -> <- Hvm1.
  + exists (vm1'.[x <- ok t])%vmap;split => // z Hin.
    case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq ?Hvm1 //;move/eqP:Hxz; SvD.fsetdec.
  exists (vm1'.[x <- undef_addr (vtype x)])%vmap;split => // z Hin.
  case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
  by rewrite !Fv.setP_neq ?Hvm1 //;move/eqP:Hxz; SvD.fsetdec.
Qed.

Lemma write_var_eq_on X x v s1 s2 vm1:
  write_var x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.add x X]  vm2 /\
    write_var x v {| emem := emem s1; evm := vm1 |} = ok {| emem := emem s2; evm := vm2 |}.
Proof.
  rewrite /write_var /=;apply: rbindP => vm2 Hset [<-].
  move=> /(set_var_eq_on Hset) [vm2' [Hvm2 ->]];exists vm2';split=>//=.
  by apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

Lemma write_lval_eq_on X x v s1 s2 vm1 :
  Sv.Subset (read_rv x) X ->
  write_lval x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
   evm s2 =[Sv.union (vrv x) X] vm2 /\
   write_lval x v {|emem:= emem s1; evm := vm1|} = ok {|emem:= emem s2; evm := vm2|}.
Proof.
  case:x => [vi ty | x | x e | x e ] /=.
  + move=> ? /write_noneP [->];rewrite /write_none=> H ?;exists vm1;split=>//.
    by case:H => [[u ->] | [-> /eqP /negbTE ->]].
  + move=> _ Hw /(write_var_eq_on Hw) [vm2 [Hvm2 Hx]];exists vm2;split=>//.
    by apply: eq_onI Hvm2;SvD.fsetdec.
  + rewrite read_eE => Hsub Hsem Hvm;move:Hsem.
    rewrite -(get_var_eq_on _ Hvm);last by SvD.fsetdec.
    rewrite (get_var_eq_on _ Hvm);last by SvD.fsetdec.
    case: s1 Hvm => sm1 svm1 Hvm1.
    rewrite (@read_e_eq_on Sv.empty vm1 svm1);first last.
    + by apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
    apply: rbindP => vx ->;apply: rbindP => ve ->;apply: rbindP => w /= ->.
    by apply: rbindP => m /= -> [<-] /=;exists vm1.
  rewrite read_eE=> Hsub Hsem Hvm;move:Hsem.
  rewrite (@on_arr_var_eq_on {| emem := emem s1; evm := vm1 |} X s1 _ _ _ Hvm);
    last by SvD.fsetdec.
  case: s1 Hvm => sm1 svm1 Hvm1.
  rewrite (@read_e_eq_on (Sv.add x Sv.empty) vm1) /=;first last.
  + by apply: eq_onI Hvm1;rewrite read_eE.
  apply: on_arr_varP => n t Htx;rewrite /on_arr_var => -> /=.
  apply: rbindP => i -> /=;apply: rbindP => ? -> /=;apply: rbindP => ? -> /=.
  apply: rbindP => ? /set_var_eq_on -/(_ _ _ Hvm1) [vm2' [Heq' ->]] [] <-.
  by exists vm2'.
Qed.

Lemma write_lvals_eq_on X xs vs s1 s2 vm1 :
  Sv.Subset (read_rvs xs) X ->
  write_lvals s1 xs vs = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.union (vrvs xs) X] vm2 /\
    write_lvals {|emem:= emem s1; evm := vm1|} xs vs = ok {|emem:= emem s2; evm := vm2|}.
Proof.
  elim: xs vs X s1 s2 vm1 => [ | x xs Hrec] [ | v vs] //= X s1 s2 vm1.
  + by move=> _ [<-] ?;exists vm1.
  rewrite read_rvs_cons => Hsub.
  apply: rbindP => s1' Hw Hws /(write_lval_eq_on _ Hw) [ |vm1' [Hvm1' ->]].
  + by SvD.fsetdec.
  have [ |vm2 [Hvm2 /= ->]]:= Hrec _ _ _ _ _ _ Hws Hvm1';first by SvD.fsetdec.
  by exists vm2;split => //;rewrite vrvs_cons;apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

End SEM.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Definition val_uincl (t:stype) : sem_t t -> sem_t t -> Prop :=
  match t as t0 return sem_t t0 -> sem_t t0 -> Prop with
  | sbool => fun b1 b2 => b1 = b2
  | sint  => fun i1 i2 => i1 = i2
  | sword => fun w1 w2 => w1 = w2
  | sarr n => fun (t1 t2:Array.array n word) =>
      (forall i v, Array.get t1 i = ok v -> Array.get t2 i = ok v)
  end.

Definition eval_uincl (t:stype) (v1 v2: exec (sem_t t)) :=
  match v1, v2 with
  | Ok  v1 , Ok   v2 => val_uincl v1 v2
  | Error ErrAddrUndef, Ok    _ => True
  | Error x, Error y => x = y
  | _      , _       => False
  end.

Definition vm_uincl (vm1 vm2:vmap) :=
  forall x, eval_uincl (vm1.[x])%vmap (vm2.[x])%vmap.

Lemma val_uincl_refl t v: @val_uincl t v v.
Proof. by elim: t v => //=. Qed.

Hint Resolve val_uincl_refl.

Lemma eval_uincl_refl t v: @eval_uincl t v v.
Proof. by case: v=> //= -[]. Qed.

Hint Resolve eval_uincl_refl.

Lemma vm_uincl_refl vm: @vm_uincl vm vm.
Proof. by done. Qed.

Hint Resolve vm_uincl_refl.

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 =>
    n1 = n2 /\ (forall i v, Array.get t1 i = ok v -> Array.get t2 i = ok v)
  | Vword w1, Vword w2 => w1 = w2
  | Vundef t, _     => t == type_of_val v2
  | _, _ => False
  end.

Lemma value_uincl_refl v: @value_uincl v v.
Proof. by case v => //=. Qed.

Hint Resolve value_uincl_refl.

Lemma is_full_array_uincl v1 v2:
  is_full_array v1 -> value_uincl v1 v2 -> v1 = v2.
Proof.
  case: v1 v2 => [?|?|??|?|?] [?|?|??|?|?] //= H; try by move=> ->.
  move=> [] <- Hget;f_equal;apply Array.eq_ext => w.
  rewrite /Array.get;case:ifPn => //.
  move=> H1;move: (H1) => /andP [] /Zle_is_le_bool H2 /Zlt_is_lt_bool H3.
  have [w' Heq]:= H _ (conj H2 H3); have := Hget _ _ Heq.
  by move: Heq;rewrite /Array.get H1 => -> ->.
Qed.

Lemma is_full_array_uincls vs1 vs2:
  List.Forall is_full_array vs1 ->
  List.Forall2 value_uincl vs1 vs2 -> vs1 = vs2.
Proof.
  move=> H1 H2;elim: H2 H1 => //= v1 v2 {vs1 vs2} vs1 vs2 Hv Hvs Hrec H;sinversion H.
  f_equal;auto using is_full_array_uincl.
Qed.

Lemma of_val_undef t t':
  of_val t (Vundef t') =
    if t == t' then undef_error else type_error.
Proof.
  case: t t' => //= [[] | [] | | []] //.
  move=> p [] // p';case:eqP => [-> | ];first by rewrite eq_refl.
  by case: eqP => // -[] ->.
Qed.

Lemma of_val_undef_ok t t' v:
  of_val t (Vundef t') <> ok v.
Proof. by rewrite of_val_undef;case:ifP. Qed.

Lemma of_val_uincl v v' t z:
  value_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_val t v' = ok z' /\ val_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | w | tv] [b' | n' | n' a' | w' | tv'] //=;
    try by move=> _ /of_val_undef_ok.
  + by move=> <- ?;exists z.
  + by move=> <- ?;exists z.
  + move=> [<- H];case: t z => //= p a1.
    by case: CEDecStype.pos_dec => //= Heq;subst=> /= -[] <-;exists a'.
  by move=> <- ?;exists z.
Qed.

Lemma to_val_uincl t (z z' : sem_t t) :
  val_uincl z z' <-> value_uincl (to_val z) (to_val z').
Proof. by case: t z z'=> //=;tauto. Qed.

Lemma value_uincl_int ve ve' z :
  value_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof.
  case:ve ve' => //=;last by move=> [].
  by move=> z0 [] //= z1 -> [] ->.
Qed.

Lemma value_uincl_word ve ve' (w:word) :
  value_uincl ve ve' -> to_word ve = ok w -> ve = w /\ ve' = w.
Proof.
  case:ve ve' => //=;last by move=> [].
  by move=> z0 [] //= z1 -> [] ->. Qed.

Lemma value_uincl_bool ve ve' b :
  value_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof.
  case:ve ve' => //=;last by move=>[].
  by move=> z0 [] //= z1 -> [] ->.
Qed.

(* TODO: MOVE *)
Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
Proof. by case: t s. Qed.

Lemma get_var_uincl x vm1 vm2 v1:
  vm_uincl vm1 vm2 ->
  get_var vm1 x = ok v1 ->
  exists v2, get_var vm2 x = ok v2 /\ value_uincl v1 v2.
Proof.
  move=> /(_ x);rewrite /get_var=> H; apply: on_vuP.
  + move=> z1 Heq1 [] <-.
    move: H;rewrite Heq1=> {Heq1}.
    case: (vm2.[x])%vmap => //= z2 Hz2;exists (to_val z2);split=> //.
    by case: (vtype x) z1 z2 Hz2.
  move=> Hvm1;move: H;rewrite Hvm1;case (vm2.[x])%vmap => //=.
  + by move=> s _ [<-];exists (to_val s) => /=;rewrite type_of_to_val.
  by move=> e <- [<-];exists (Vundef (vtype x)).
Qed.

Lemma  get_vars_uincl (xs:seq var_i) vm1 vm2 vs1:
  vm_uincl vm1 vm2 ->
  mapM (fun x => get_var vm1 (v_var x)) xs = ok vs1 ->
  exists vs2,
    mapM (fun x => get_var vm2 (v_var x)) xs = ok vs2 /\ List.Forall2 value_uincl vs1 vs2.
Proof.
  move=> Hvm;elim: xs vs1 => [ | x xs Hrec] /= ?.
  + move=> [<-];exists [::];split=>//; constructor.
  apply: rbindP => v1 /(get_var_uincl Hvm) [v2 [-> ?]].
  apply: rbindP => vs1 /Hrec [vs2 [-> ?]] [] <- /=;exists (v2::vs2);split=>//.
  by constructor.
Qed.

Lemma vuincl_sem_op2_b o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_b o ve1 ve2 = ok v1 ->
  sem_op2_b o ve1' ve2' = ok v1.
Proof.
  rewrite /sem_op2_b /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_bool Hvu1) [] _ ->.
  by apply: rbindP => z2 /(value_uincl_bool Hvu2) [] _ -> [] <-.
Qed.

Lemma vuincl_sem_op2_i o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_i o ve1 ve2 = ok v1 ->
  sem_op2_i o ve1' ve2' = ok v1.
Proof.
  rewrite /sem_op2_i /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_int Hvu1) [] _ ->.
  by apply: rbindP => z2 /(value_uincl_int Hvu2) [] _ -> [] <-.
Qed.

Lemma vuincl_sem_op2_w o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_w o ve1 ve2 = ok v1 ->
  sem_op2_w o ve1' ve2' = ok v1.
Proof.
  rewrite /sem_op2_w /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_word Hvu1) [] _ ->.
  by apply: rbindP => z2 /(value_uincl_word Hvu2) [] _ -> [] <- /=.
Qed.

Lemma vuincl_sem_op2_ib o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_ib o ve1 ve2 = ok v1 ->
  sem_op2_ib o ve1' ve2' = ok v1.
Proof.
  rewrite /sem_op2_ib /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_int Hvu1) [] _ ->.
  by apply: rbindP => z2 /(value_uincl_int Hvu2) [] _ -> [] <- /=.
Qed.

Lemma vuincl_sem_op2_wb o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_wb o ve1 ve2 = ok v1 ->
  sem_op2_wb o ve1' ve2' = ok v1.
Proof.
  rewrite /sem_op2_wb /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_word Hvu1) [] _ ->.
  by apply: rbindP => z2 /(value_uincl_word Hvu2) [] _ -> [] <- /=.
Qed.

Lemma vuincl_sem_sop2 o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' ->
  sem_sop2 o ve1 ve2 = ok v1 ->
  sem_sop2 o ve1' ve2' = ok v1.
Proof.
  case:o => [||[]|[]|[]|||||||[]|[]|[]|[]|[]|[]]/=;
   eauto using vuincl_sem_op2_i, vuincl_sem_op2_w, vuincl_sem_op2_b, vuincl_sem_op2_ib,
    vuincl_sem_op2_wb.
Qed.

Lemma vuincl_sem_sop1 o ve1 ve1' v1 :
  value_uincl ve1 ve1' ->
  sem_sop1 o ve1 = ok v1 ->
  sem_sop1 o ve1' = ok v1.
Proof.
  case: o;rewrite /= /sem_op1_b /sem_op1_w /mk_sem_sop1 => Hu;
    apply: rbindP => z Hz [] <-.
  + by have [z' [-> /= <- ]]:= of_val_uincl Hu Hz.
  by have [z' [-> /= <- ]]:= of_val_uincl Hu Hz.
Qed.

Lemma type_of_val_uincl v1 v2:
  value_uincl v1 v2 ->
  type_of_val v1 = type_of_val v2.
Proof.
  move: v1 v2=> [b|z|n a|w|s] [b'|z'|n' a'|w'|s'] //=; try by apply/eqP.
  by move=> [-> _].
Qed.

Lemma sem_pexpr_uincl s1 vm2 e v1:
  vm_uincl s1.(evm) vm2 ->
  sem_pexpr s1 e = ok v1 ->
  exists v2, sem_pexpr (Estate s1.(emem) vm2) e = ok v2 /\ value_uincl v1 v2.
Proof.
  move=> Hu; elim: e v1=>//=[z|b|e He|x|x p Hp|x p Hp|o e He|o e1 He1 e2 He2|e He e1 He1 e2 He2 ] v1.
  + by move=> [] <-;exists z.
  + by move=> [] <-;exists b.
  + apply: rbindP => z;apply: rbindP => ve /He [] ve' [] -> Hvu Hto [] <-.
    by case: (value_uincl_int Hvu Hto) => ??;subst; exists (Vword (I64.repr z)).
  + by apply get_var_uincl.
  + apply on_arr_varP => n t Htx;rewrite /on_arr_var=> /(get_var_uincl Hu) [v2 [->]].
    case: v2 => //= ? t' [] ? Htt';subst.
    apply: rbindP => z;apply: rbindP => vp /Hp [] vp' [] -> /= Hvu Hto.
    case: (value_uincl_int Hvu Hto) => ??;subst.
    apply: rbindP=> w /Htt' Hget [] <- /=.
    by exists w;rewrite Hget.
  + apply: rbindP => w1;apply: rbindP => vx /(get_var_uincl Hu) [vx' [->]].
    move=> /value_uincl_word H/H{H}[_ ->].
    apply: rbindP => wp;apply: rbindP => vp /Hp [] vp' [] ->.
    by move=> /value_uincl_word Hvu /Hvu [_ ->] /=;exists v1.
  + apply: rbindP => ve1 /He [] ve1' [] -> /vuincl_sem_sop1 Hvu1 /Hvu1.
    by exists v1.
  + apply: rbindP => ve1 /He1 [] ve1' [] -> /vuincl_sem_sop2 Hvu1.
    apply: rbindP => ve2 /He2 [] ve2' [] -> /Hvu1 Hvu2 /Hvu2.
    by exists v1.
  apply: rbindP => b;apply:rbindP => wb /He [] ve' [] -> Hue'.
  move=> /value_uincl_bool -/(_ _ Hue') [??];subst wb ve' => /=.
  apply: rbindP=> v2 /He1 [] v2' [] -> Hv2'.
  apply: rbindP=> v3 /He2 [] v3' [] -> Hv3'.
  case Ht: (type_of_val _ == _)=> // -[]<- /=.
  rewrite -(type_of_val_uincl Hv2') -(type_of_val_uincl Hv3') Ht.
  eexists; split=> //.
  by case: (b).
Qed.

Lemma sem_pexprs_uincl s1 vm2 es vs1:
  vm_uincl s1.(evm) vm2 ->
  sem_pexprs s1 es  = ok vs1 ->
  exists vs2, sem_pexprs (Estate s1.(emem) vm2) es = ok vs2 /\
              List.Forall2 value_uincl vs1 vs2.
Proof.
  rewrite /sem_pexprs; move=> Hvm;elim: es vs1 => [ | e es Hrec] vs1 /=.
  + by move=> [] <-;eauto.
  apply: rbindP => ve /(sem_pexpr_uincl Hvm) [] ve' [] -> ?.
  by apply: rbindP => ys /Hrec [vs2 []] /= -> ? [] <- /=;eauto.
Qed.

Definition is_w_or_b t :=
  match t with
  | sbool | sword => true
  | _             => false
  end.

Lemma vuincl_sopn ts o vs vs' v :
  all is_w_or_b ts ->
  List.Forall2 value_uincl vs vs' ->
  app_sopn ts o vs = ok v ->
  exists v' : values,
     app_sopn ts o vs' = ok v' /\ List.Forall2 value_uincl v v'.
Proof.
  elim: ts o vs vs' => /= [ | t ts Hrec] o vs vs' Hall Hu;sinversion Hu => //=.
  + move => ->;exists v;auto using List_Forall2_refl.
  move: Hall=> /andP [];case: t o => //= o _ Hall;apply:rbindP.
  + by move=> b /(value_uincl_bool H) [] _ -> /= /(Hrec _ _ _ Hall H0).
  by move=> w /(value_uincl_word H) [] _ -> /= /(Hrec _ _ _ Hall H0).
Qed.

Lemma vuincl_sem_opn o vs vs' v :
  List.Forall2 value_uincl vs vs' -> sem_sopn o vs = ok v ->
  exists v', sem_sopn o vs' = ok v' /\ List.Forall2  value_uincl v v'.
Proof.
  rewrite /sem_sopn;case: o => //;try apply vuincl_sopn=> //.
  move: vs=> [] // vs1 [] // vs2 [] // vs3 [] //.
  move: vs'=> [|vs'1].
  + move=> Hu; sinversion Hu.
  move=> [|vs'2].
  + move=> Hu; sinversion Hu; sinversion H4.
  move=> [|vs'3].
  + move=> Hu; sinversion Hu; sinversion H4; sinversion H6.
  move=> [//|].
  + move=> H; sinversion H; sinversion H5; sinversion H6.
    apply: rbindP=> b /(value_uincl_bool H3) [] _ ->.
    case: (b)=> /=.
    + apply: rbindP=> v2 /(value_uincl_word H2) [] _ -> []<-.
      eexists; split=> //.
      apply: List.Forall2_cons=> //.
    + apply: rbindP=> v3 /(value_uincl_word H4) [] _ -> []<-.
      eexists; split=> //.
      apply: List.Forall2_cons=> //.
  move=> a l H.
  sinversion H; sinversion H5; sinversion H6; sinversion H7.
Qed.

Lemma set_vm_uincl vm vm' x z z' :
  vm_uincl vm vm' ->
  val_uincl z z' ->
  vm_uincl (vm.[x <- ok z])%vmap (vm'.[x <- ok z'])%vmap.
Proof.
  move=> Hvm Hz y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.

(* TODO : MOVE *)
Lemma of_val_error t v:
  of_val t v = undef_error -> v = Vundef t.
Proof.
  case: t v => [||p|] [] //=.
  + by move=> []. + by move=> [].
  + by move=> n a;case: CEDecStype.pos_dec => [? | ] //;subst p.
  + by move=> [] // p';case: eqP => [-> | ].
  by move=> [].
Qed.

Lemma of_val_type_of v :
  (exists v', of_val (type_of_val v) v = ok v') \/
  of_val (type_of_val v) v =  Error ErrAddrUndef.
Proof.
  case: v => //=;try by left;eauto.
  + move=> n a;case: CEDecStype.pos_dec (@CEDecStype.pos_dec_r n n) => /=.
    + by move=> ??;left;eauto.
    by move=> b /(_ b (refl_equal _)) /eqP.
  move=> [||p|];right;try done.
  by rewrite /= eq_refl.
Qed.

Lemma eval_uincl_undef t v : eval_uincl (undef_addr t) (ok v).
Proof.
  by case: t v => //= p v i w H; have := Array.getP_empty H.
Qed.

Lemma set_var_uincl vm1 vm1' vm2 x v v' :
  vm_uincl vm1 vm1' ->
  value_uincl v v' ->
  set_var vm1 x v = ok vm2 ->
  exists vm2', set_var vm1' x v' = ok vm2' /\ vm_uincl vm2 vm2'.
Proof.
  (move=> Hvm Hv;apply set_varP;rewrite /set_var) => [t | /negbTE ->].
  + move=> /(of_val_uincl Hv) [z' [-> ?]] [] <- /=.
    by exists (vm1'.[x <- ok z'])%vmap;split=>//; apply set_vm_uincl.
  move=> /of_val_error Heq;move: Hv;rewrite Heq /= => /eqP.
  case: x Heq=> [ty xn] /= _ ->.
  set x := {|vtype := _ |};rewrite /on_vu.
  case: (of_val_type_of v') => [ [v1 ->] | ->] <-;eexists;split;eauto.
  + move=> z /=;case: (x =P z) => [<- |/eqP ? ].
    + rewrite !Fv.setP_eq;apply: eval_uincl_undef.
    by rewrite !Fv.setP_neq.
  move=> z /=;case: (x =P z) => [<- |/eqP ? ].
  + by rewrite !Fv.setP_eq.
  by rewrite !Fv.setP_neq.
Qed.

Lemma Array_set_uincl n (a1 a2 a1':Array.array n word) i v:
  @val_uincl (sarr n) a1 a2 ->
  Array.set a1 i v = ok a1' ->
  exists a2', Array.set a2 i v = ok a2' /\ @val_uincl (sarr n) a1' a2'.
Proof.
  rewrite /Array.set;case:ifP=> //= ? H [] <-.
  exists (FArray.set a2 i (ok v));split => // i' v';move: (H i' v').
  rewrite /Array.get;case:ifP=> //= Hbound.
  by rewrite !FArray.setP;case:ifP.
Qed.

Lemma write_var_uincl s1 s2 vm1 v1 v2 x :
  vm_uincl (evm s1) vm1 ->
  value_uincl v1 v2 ->
  write_var x v1 s1 = ok s2 ->
  exists vm2 : vmap,
    write_var x v2 {| emem := emem s1; evm := vm1 |} =
    ok {| emem := emem s2; evm := vm2 |} /\ vm_uincl (evm s2) vm2.
Proof.
  move=> Hvm1 Hv;rewrite /write_var;apply: rbindP=> vm2 /=.
  by move=> /(set_var_uincl Hvm1 Hv) [vm2' [-> ?]] [] <- /=;exists vm2'.
Qed.

Lemma write_vars_uincl s1 s2 vm1 vs1 vs2 xs :
  vm_uincl (evm s1) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_vars xs vs1 s1 = ok s2 ->
  exists vm2 : vmap,
    write_vars xs vs2 {| emem := emem s1; evm := vm1 |} =
    ok {| emem := emem s2; evm := vm2 |} /\ vm_uincl (evm s2) vm2.
Proof.
  elim: xs s1 vm1 vs1 vs2 => /= [ | x xs Hrec] s1 vm1 vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(write_var_uincl Hvm Hv) [] vm2 [] -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma uincl_write_none s2 v1 v2 s s' t :
  value_uincl v1 v2 ->
  write_none s t v1 = ok s' ->
  write_none s2 t v2 = ok s2.
Proof.
  move=> Hv /write_noneP [_] H;rewrite /write_none.
  case:H.
  + by move=> [u] /(of_val_uincl Hv) [u' [-> _]].
  move=> []/of_val_error ? /eqP /negbTE ->;subst v1.
  move: Hv => /= /eqP ->.
  by case: (of_val_type_of v2) => [[?]|] ->.
Qed.

Lemma write_uincl s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  write_lval r v1 s1 = ok s2 ->
  exists vm2,
    write_lval r v2 (Estate (emem s1) vm1) = ok (Estate (emem s2) vm2) /\
    vm_uincl s2.(evm) vm2.
Proof.
  move=> Hvm1 Hv;case:r => [xi ty | x | x p | x p] /=.
  + move=> H; have [-> _]:= write_noneP H.
    by rewrite (uincl_write_none _ Hv H);exists vm1.
  + by apply write_var_uincl.
  + apply: rbindP => vx1; apply: rbindP => vx /(get_var_uincl Hvm1) [vx2 [-> Hvx]].
    move=> /(value_uincl_word Hvx) [] _ -> {Hvx vx} /=.
    apply: rbindP => ve; apply: rbindP => ve' /(sem_pexpr_uincl Hvm1) [ve''] [] -> Hve.
    move=> /(value_uincl_word Hve) [] _ -> /=.
    apply: rbindP => w /(value_uincl_word Hv) [] _ -> /=.
    by apply: rbindP => m' -> [] <- /=;eauto.
  apply: on_arr_varP => n a Htx /(get_var_uincl Hvm1).
  rewrite /on_arr_var => -[] vx [] /= -> /=;case: vx => //= n0 t0 [] ? Ht0;subst.
  apply: rbindP => i;apply: rbindP=> vp /(sem_pexpr_uincl Hvm1) [vp' [-> Hvp]] /=.
  move=>  /(value_uincl_int Hvp) [] _ -> /=.
  apply: rbindP => v /(value_uincl_word Hv) [] _ -> /=.
  apply: rbindP => t=> /(Array_set_uincl Ht0).
  move=> [] t' [-> Ht];apply: rbindP => vm'.
  have Hut: value_uincl (Varr t) (Varr t') by split.
  by move=> /(set_var_uincl Hvm1 Hut) /= [vm2' [-> ?]] [] <- /=;eauto.
Qed.

Lemma writes_uincl s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals s1 r v1 = ok s2 ->
  exists vm2,
    write_lvals (Estate (emem s1) vm1) r v2 = ok (Estate (emem s2) vm2) /\
    vm_uincl s2.(evm) vm2.
Proof.
  elim: r v1 v2 s1 s2 vm1 => [ | r rs Hrec] ?? s1 s2 vm1 Hvm1 /= [] //=.
  + by move=> [] <-;eauto.
  move=> v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP => z /(write_uincl Hvm1 Hv) [] vm2 [-> Hvm2].
  by move=> /(Hrec _ _ _ _ _ Hvm2 Hforall).
Qed.

Lemma write_vars_lvals xs vs s1:
  write_vars xs vs s1 = write_lvals s1 [seq Lvar i | i <- xs] vs.
Proof.
  rewrite /write_vars /write_lvals.
  elim: xs vs s1 => [ | x xs Hrec] [ | v vs] //= s1.
  by case: write_var => //=.
Qed.

Lemma sem_pexprs_get_var s xs :
  sem_pexprs s [seq Pvar i | i <- xs] = mapM (fun x : var_i => get_var (evm s) x) xs.
Proof.
  rewrite /sem_pexprs;elim: xs=> //= x xs Hrec.
  by case: get_var => //= v;rewrite Hrec.
Qed.

Section UNDEFINCL.

Variable (p:prog).

Let Pc s1 c s2 :=
  forall vm1 ,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem p {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pi_r s1 i s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem_i p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pi s1 i s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem_I p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pfor (i:var_i) zs s1 c s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem_for p i zs {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pfun m1 fd vargs m2 vres :=
  forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    sem_call p m1 fd vargs' m2 vres.

Local Lemma Hnil s : @Pc s [::] s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hcons s1 s2 s3 i c :
  sem_I p s1 i s2 -> Pi s1 i s2 ->
  sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
Proof.
  move=> _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Local Lemma HmkI ii i s1 s2 : sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
Proof. by move=> _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.

Local Lemma Hasgn s1 s2 x tag e :
  Let v := sem_pexpr s1 e in write_lval x v s1 = ok s2 ->
  Pi_r s1 (Cassgn x tag e) s2.
Proof.
  move=> Hs2 vm1 Hvm1;apply:rbindP Hs2 => z /(sem_pexpr_uincl Hvm1) [] z' [] Hz' Hz.
  move=> /(write_uincl Hvm1 Hz) [vm2 []] Hw ?;exists vm2;split=> //.
  by constructor;rewrite Hz' /= Hw.
Qed.

Local Lemma Hopn s1 s2 o xs es:
  Let x := Let x := sem_pexprs s1 es in sem_sopn o x in
  write_lvals s1 xs x = ok s2 -> Pi_r s1 (Copn xs o es) s2.
Proof.
  move=> H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(sem_pexprs_uincl Hvm1) [] vs' [] H1 H2.
  move=> /(vuincl_sem_opn H2) [] rs' [] H3 H4.
  move=> /(writes_uincl Hvm1 H4) [] vm2 [] ??.
  exists vm2;split => //;constructor.
  by rewrite H1 /= H3.
Qed.

Local Lemma Hif_true s1 s2 e c1 c2 :
  Let x := sem_pexpr s1 e in to_bool x = ok true ->
  sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(sem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_true;rewrite // H1.
Qed.

Local Lemma Hif_false s1 s2 e c1 c2 :
  Let x := sem_pexpr s1 e in to_bool x = ok false ->
  sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(sem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
  sem p s1 c s2 -> Pc s1 c s2 ->
  Let x := sem_pexpr s2 e in to_bool x = ok true ->
  sem p s2 c' s3 -> Pc s2 c' s3 ->
  sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
Proof.
  move=> _ Hc H _ Hc' _ Hw vm1 Hvm1;apply: rbindP H => v.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  move=> /(sem_pexpr_uincl Hvm2) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst.
  have [vm3 [H4 /Hw [vm4] [??]]]:= Hc' _ Hvm2;exists vm4;split => //.
  by eapply Ewhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false s1 s2 c e c' :
  sem p s1 c s2 -> Pc s1 c s2 ->
  Let x := sem_pexpr s2 e in to_bool x = ok false ->
  Pi_r s1 (Cwhile c e c') s2.
Proof.
  move=> _ Hc H vm1 Hvm1; apply: rbindP H => v.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  move=> /(sem_pexpr_uincl Hvm2) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst.
  by exists vm2;split=> //;apply: Ewhile_false=> //;rewrite H1.
Qed.

Local Lemma Hfor s1 s2 (i : var_i) d lo hi c (vlo vhi : Z) :
  Let x := sem_pexpr s1 lo in to_int x = ok vlo ->
  Let x := sem_pexpr s1 hi in to_int x = ok vhi ->
  sem_for p i (wrange d vlo vhi) s1 c s2 ->
  Pfor i (wrange d vlo vhi) s1 c s2 ->
  Pi_r s1 (Cfor i (d, lo, hi) c) s2.
Proof.
  move=> H H' _ Hfor vm1 Hvm1;apply: rbindP H => ?.
  move=> /(sem_pexpr_uincl Hvm1) [] ? [] H1 H2.
  move=> /(value_uincl_int H2) [] ??;subst.
  apply: rbindP H' => ?.
  move=> /(sem_pexpr_uincl Hvm1) [] ? [] H3 H4.
  move=> /(value_uincl_int H4) [] ??;subst.
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil s i c : Pfor i [::] s c s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w : Z) (ws : seq Z) c :
  write_var i w s1 = ok s1' ->
  sem p s1' c s2 -> Pc s1' c s2 ->
  sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
Proof.
  move=> Hi _ Hc _ Hf vm1 Hvm1.
  have [vm1' [Hi' /Hc]] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs :
  sem_pexprs s1 args = ok vargs ->
  sem_call p (emem s1) fn vargs m2 vs ->
  Pfun (emem s1) fn vargs m2 vs ->
  write_lvals {| emem := m2; evm := evm s1 |} xs vs = ok s2 ->
  Pi_r s1 (Ccall ii xs fn args) s2.
Proof.
  move=> Hargs Hcall Hfd Hxs vm1 Hvm1.
  have [vargs' [Hsa /Hfd Hc]]:= sem_pexprs_uincl Hvm1 Hargs.
  have Hvm1' : vm_uincl (evm {| emem := m2; evm := evm s1 |}) vm1 by done.
  have [vm2' [??]]:= writes_uincl Hvm1' (List_Forall2_refl vs value_uincl_refl) Hxs.
  exists vm2';split=>//;econstructor;eauto.
Qed.

Local Lemma Hproc m1 m2 fn fd vargs s1 vm2 vres:
  get_fundef p fn = Some fd ->
  write_vars (f_params fd) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
  sem p s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
  Pc s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
  mapM (fun x : var_i => get_var vm2 x) (f_res fd) = ok vres ->
  List.Forall is_full_array vres ->
  Pfun m1 fn vargs m2 vres.
Proof.
  move=> Hget Hargs Hsem Hrec Hmap Hfull vargs' Uargs.
  have [vm1 [Hargs' Hvm1]]:= write_vars_uincl (vm_uincl_refl _) Uargs Hargs.
  have [vm2' /= [] Hsem' Uvm2]:= Hrec _ Hvm1.
  have [vs2 [Hvs2]] := get_vars_uincl Uvm2 Hmap.
  move=> /(is_full_array_uincls Hfull) ?;subst.
  econstructor;eauto.
Qed.

Lemma sem_call_uincl vargs m1 f m2 vres vargs':
  List.Forall2 value_uincl vargs vargs' ->
  sem_call p m1 f vargs m2 vres ->
  sem_call p m1 f vargs' m2 vres.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_i_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_i p s1 i s2 ->
  exists vm2,
    sem_i p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_i_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_I_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_I p s1 i s2 ->
  exists vm2,
    sem_I p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_I_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_uincl s1 c s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem p s1 c s2 ->
  exists vm2,
    sem p {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

End UNDEFINCL.

Lemma eq_exprP s e1 e2 : eq_expr e1 e2 -> sem_pexpr s e1 = sem_pexpr s e2.
Proof.
  elim: e1 e2=> [z  | b  | e He | x  | x e He | x e He | o e  He | o e1 He1 e2 He2 | e He e1 He1 e2 He2]
                [z' | b' | e'   | x' | x' e'  | x' e'  | o' e' | o' e1' e2' | e' e1' e2'] //=.
  + by move=> /eqP ->.   + by move=> /eqP ->.
  + by move=> /He ->.    + by move=> /eqP ->.
  + by move=> /andP [] /eqP -> /He ->.
  + by move=> /andP [] /eqP -> /He ->.
  + by move=> /andP[]/eqP -> /He ->.
  + by move=> /andP[]/andP[] /eqP -> /He1 -> /He2 ->.
  by move=> /andP[]/andP[] /He -> /He1 -> /He2 ->.
Qed.
