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
Require Export array expr low_memory.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Values
  * -------------------------------------------------------------------- *)

Variant value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall s n, Array.array n (word s) -> value
  | Vword  : forall s, word s -> value
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

Definition truncate_word (s s':wsize) (w:word s') : exec (word s) := 
   if (s <= s')%CMP then ok (zero_extend s w) else type_error.

Definition to_word (s: wsize) (v: value) : exec (word s) :=
  match v with
  | Vword s' w        => truncate_word s w
  | Vundef (sword s') => Error (if (s <= s')%CMP then ErrAddrUndef else ErrType)
  | _                 => type_error
  end.

Notation to_pointer := (to_word Uptr).

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr s n => Array.array n (word s)
  | sword s  => word s
  end.

Definition to_arr s n v : exec (sem_t (sarr s n)) :=
  match v with
  | Varr s' n' t =>
    match wsize_eq_dec s' s with
    | left eqw =>
      match CEDecStype.pos_dec n' n with
      | left eqn => 
        let t := eq_rect n' (fun p => Array.array p (word s')) t n eqn in
        let t := eq_rect s' (fun p => Array.array n (word p)) t s eqw in
        ok t
      | _      => type_error
      end
    | _ => type_error
    end
  | Vundef (sarr s' n') => Error (if (s == s') && (n == n') then ErrAddrUndef else ErrType)
  | _                => type_error
  end.

Definition vundef_type (t:stype) :=
  match t with
  | sword _ => sword8
  | _       => t
  end.

Definition type_of_val (v:value) : stype :=
  match v with
  | Vbool _     => sbool
  | Vint  _     => sint
  | Varr s n _  => sarr s n
  | Vword s _   => sword s
  | Vundef t    => vundef_type t
  end.

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool    => to_bool
  | sint     => to_int
  | sarr s n => to_arr s n
  | sword s  => to_word s
  end.

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | sbool    => Vbool
  | sint     => Vint
  | sarr s n => @Varr s n 
  | sword s  => @Vword s
  end.

Definition truncate_val (ty: stype) (v: value) : exec value :=
  of_val ty v >>= λ x, ok (to_val x).

Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
Proof. by case: t s. Qed.

Definition check_ty_val (ty:stype) (v:value) :=
  subtype ty (type_of_val v).

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t (fun t => exec (sem_t t))).

Definition undef_addr t :=
  match t return exec (sem_t t) with
  | sbool | sint | sword _ => undef_error
  | sarr s n => ok (@Array.empty _ n)
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
  (v = Error ErrAddrUndef -> fu = ok r -> P) ->
  on_vu fv fu v = ok r -> P.
Proof. by case: v => [a | []] Hfv Hfu //=;[case; apply: Hfv | apply Hfu]. Qed.

Definition get_var (m:vmap) x :=
  on_vu (@to_val (vtype x)) (ok (Vundef (vtype x))) (m.[x]%vmap).

(* We do not allows to assign to a variable of type word an undef value *)
Definition set_var (m:vmap) x v : exec vmap :=
  on_vu (fun v => m.[x<-ok v]%vmap)
        (if is_sword x.(vtype) then type_error
         else ok m.[x<-undef_addr x.(vtype)]%vmap)
        (of_val (vtype x) v).

Lemma set_varP (m m':vmap) x v P :
   (forall t, of_val (vtype x) v = ok t -> m.[x <- ok t]%vmap = m' -> P) ->
   ( ~~is_sword x.(vtype)  ->
     of_val (vtype x) v = Error ErrAddrUndef ->
     m.[x<-undef_addr x.(vtype)]%vmap = m' -> P) ->
   set_var m x v = ok m' -> P.
Proof.
  move=> H1 H2;apply on_vuP => //.
  by case:ifPn => // neq herr [];apply : H2.
Qed.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition lprod ts tr :=
  foldr (fun t tr => t -> tr) tr ts.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Definition sem_shift (shift:forall {s}, word s -> Z -> word s) s (v:word s) (i:u8) :=
  let i :=  wunsigned (wand i (x86_shift_mask s)) in
  shift v i.

Definition sem_shr {s} := @sem_shift (@wshr) s.
Definition sem_sar {s} := @sem_shift (@wsar) s.
Definition sem_shl {s} := @sem_shift (@wshl) s.

Definition sem_sop1_typed (o: sop1) :
  let t := type_of_op1 o in
  sem_t t.1 → sem_t t.2 :=
  match o with
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

Import Memory.

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition on_arr_var A (s:estate) (x:var) (f:forall sz n, Array.array n (word sz)-> exec A) :=
  Let v := get_var s.(evm) x in
  match v with
  | Varr sz n t => f sz n t
  | _ => type_error
  end.

Notation "'Let' ( sz , n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@on_arr_var _ s x (fun sz n (t:Array.array n (word sz)) => body)) (at level 25, s at level 0).

Lemma on_arr_varP A (f : forall sz n, Array.array n (word sz) -> exec A) v s x P:
  (forall sz n t, vtype x = sarr sz n ->
               get_var (evm s) x = ok (@Varr sz n t) ->
               f sz n t = ok v -> P) ->
  on_arr_var s x f = ok v -> P.
Proof.
  rewrite /on_arr_var=> H;apply: rbindP => vx.
  case: x H => -[ | | sz n | sz ] nx;rewrite /get_var => H;
    case Heq : ((evm s).[_])%vmap => [v' | e] //=.
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]; apply: H => //;rewrite Heq. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
Qed.

Definition Varr_inj sz sz' n n' t t' (e: @Varr sz n t = @Varr sz' n' t') :
  n = n' ∧
  ∃ e : sz = sz', eq_rect sz (λ s, Array.array n (word s)) t sz' e = t' :=
  let 'Logic.eq_refl := e in conj erefl (ex_intro _ erefl erefl).

Lemma Varr_inj1 sz n t t' : @Varr sz n t = @Varr sz n t' -> t = t'.
Proof.
  move => /Varr_inj [_] [] e.
  by rewrite (Eqdep_dec.UIP_dec wsize_eq_dec e erefl).
Qed.

Definition Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Definition glob_def : Type := global * value.
Notation glob_defs := (seq glob_def).

Definition get_global_value (gd: glob_defs) (g: global) : option value :=
  assoc gd g.

Definition get_global gd g : exec value :=
  if get_global_value gd g is Some (Vword sz w as v)
  then Let _ := assert (sz == size_of_global g) ErrType in ok v
  else type_error.

Lemma get_globalI gd g v :
  get_global gd g = ok v →
  exists2 w : word (size_of_global g), get_global_value gd g = Some (Vword w) & v = Vword w.
Proof.
  rewrite /get_global; case: get_global_value => // - [] // sz w.
  t_xrbindP => _ /assertP /eqP ??; subst; eauto.
Qed.

Definition is_defined (v: value) : bool :=
  if v is Vundef _ then false else true.

Section SEM_PEXPR.

Context (gd: glob_defs).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Parr_init sz n => ok (@Varr sz n (Array.empty n))
  | Pcast sz e  =>
    Let z := sem_pexpr s e >>= to_int in
    ok (Vword (wrepr sz z))
  | Pvar v => get_var s.(evm) v
  | Pglobal g => get_global gd g
  | Pget x e =>
      Let (sz, n, t) := s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := Array.get t i in
      ok (Vword w)
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := read_mem s.(emem) (w1 + w2) sz in
    ok (@to_val (sword sz) w)
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
    if type_of_val v1 == type_of_val v2 then
    if is_defined v1 && is_defined v2 then
      ok (if b then v1 else v2)
    else undef_error
    else type_error
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok ({| emem := s.(emem); evm := vm |}).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s:estate) ty v :=
  on_vu (fun v => s) (if is_sword ty then type_error else ok s)
          (of_val ty v).

Definition write_lval (l:lval) (v:value) (s:estate) : exec estate :=
  match l with
  | Lnone _ ty => write_none s ty v
  | Lvar x => write_var x v s
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let ve := sem_pexpr s e >>= to_pointer in
    let p := (vx + ve)%R in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok {| emem := m;  evm := s.(evm) |}
  | Laset x i =>
    Let (sz,n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word sz v in
    Let t := Array.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr sz n) t) in
    ok ({| emem := s.(emem); evm := vm |})
  end.

Definition write_lvals (s:estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.

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

Definition SF_of_word sz (w : word sz) :=
  msb w.

Definition PF_of_word sz (w : word sz) :=
  lsb w.

Definition ZF_of_word sz (w : word sz) :=
  w == 0%R.

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_bwop sz (w : word sz) :=
  (*  OF   ; CF   ; SF          ; PF          ; ZF          ] *)
  [:: false; false; SF_of_word w; PF_of_word w; ZF_of_word w].

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_aluop sz (w : word sz) (vu vs : Z) :=
  (*  OF                  ; CF                    *)
  [:: wsigned  w != vs; wunsigned w != vu;
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
Definition rflags_of_aluop_nocf sz (w : word sz) (vs : Z) :=
  (*  OF                  *)
  [:: wsigned   w != vs;
  (*  SF          ; PF          ; ZF          ] *)
      SF_of_word w; PF_of_word w; ZF_of_word w ].

Definition flags_w (bs:seq bool) sz (w: word sz) : exec values :=
  ok ((map Vbool bs) ++ [:: Vword w]).

Definition rflags_of_aluop_w sz (w : word sz) (vu vs : Z) : exec values :=
  flags_w (rflags_of_aluop w vu vs) w.

Definition rflags_of_aluop_nocf_w sz (w : word sz) (vs : Z) : exec values :=
  flags_w (rflags_of_aluop_nocf w vs) w.

Definition rflags_of_bwop_w sz (w : word sz) : exec values :=
  flags_w (rflags_of_bwop w) w.

Definition vbools bs : exec values := ok (List.map Vbool bs).

(* -------------------------------------------------------------------- *)


Definition x86_MOV sz (x: word sz) : exec values :=
  Let _ := check_size_8_64 sz in
  ok [:: Vword x].

Definition x86_MOVSX szo szi (x: word szi) : exec values :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | U32 => assert (szo == U64) ErrType
    | _ => type_error
    end in
  ok [:: Vword (sign_extend szo x) ].

Definition x86_MOVZX szo szi (x: word szi) : exec values :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | _ => type_error
    end in
  ok [:: Vword (zero_extend szo x) ].

Definition x86_add {sz} (v1 v2 : word sz) :=
  Let _ := check_size_8_64 sz in
  rflags_of_aluop_w
    (v1 + v2)%R
    (wunsigned v1 + wunsigned v2)%Z
    (wsigned   v1 + wsigned   v2)%Z.

Definition x86_sub {sz} (v1 v2 : word sz) :=
  Let _ := check_size_8_64 sz in
  rflags_of_aluop_w
    (v1 - v2)%R
    (wunsigned v1 - wunsigned v2)%Z
    (wsigned   v1 - wsigned   v2)%Z.

Definition x86_mul {sz} (v1 v2: word sz): exec values :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhu v1 v2 in
  let ov := wdwordu hi lo in
  let ov := (ov >? wbase sz - 1)%Z in
  ok (rflags_of_mul ov ++ [::Vword hi; Vword lo]).

Definition x86_imul_overflow sz (hi lo: word sz) : bool :=
  let ov := wdwords hi lo in
  (ov <? -wbase sz)%Z || (ov >? wbase sz - 1)%Z.

Definition x86_imul {sz} (v1 v2: word sz) : exec values:=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_imul_overflow hi lo in
  ok (rflags_of_mul ov ++ [::Vword hi; Vword lo]).

Definition x86_imult {sz} (v1 v2: word sz) : exec values:=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_imul_overflow hi lo in
  ok (rflags_of_mul ov ++ [::Vword lo]).

Definition x86_div {sz} (hi lo dv: word sz) : exec values:=
  Let _  := check_size_16_64 sz in
  let dd := wdwordu hi lo in
  let dv := wunsigned dv in
  let q  := (dd  /  dv)%Z in
  let r  := (dd mod dv)%Z in
  let ov := (q >? wmax_unsigned sz)%Z in

  if (dv == 0)%Z || ov then type_error else

  ok (rflags_of_div ++ [:: Vword (wrepr sz q); Vword (wrepr sz r)]).

Definition x86_idiv {sz} (hi lo dv: word sz) : exec values :=
  Let _  := check_size_16_64 sz in
  let dd := wdwords hi lo in
  let dv := wsigned dv in
  let q  := (Z.quot dd dv)%Z in
  let r  := (Z.rem  dd dv)%Z in
  let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in

  if (dv == 0)%Z || ov then type_error else

  ok (rflags_of_div ++ [:: Vword (wrepr sz q); Vword (wrepr sz r)]).

Definition x86_cqo {sz} (w:word sz) : exec values := 
  Let _ := check_size_16_64 sz in
  let r : word sz := (if msb w then -1 else 0)%R in
  ok [::Vword r].
  
Definition add_carry sz (x y c: Z) : word sz :=
  wrepr sz (x + y + c).

Definition x86_adc {sz} (v1 v2 : word sz) (c: bool) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  rflags_of_aluop_w
    (add_carry sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 + wunsigned v2 + c)%Z
    (wsigned   v1 + wsigned   v2 + c)%Z.

Definition sub_borrow sz (x y c: Z) : word sz :=
  wrepr sz (x - y - c).

Definition x86_sbb {sz} (v1 v2 : word sz) (c:bool) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  rflags_of_aluop_w
    (sub_borrow sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 - (wunsigned v2 + c))%Z
    (wsigned   v1 - (wsigned   v2 + c))%Z.

Definition x86_neg {sz} (w: word sz) :=
  Let _  := check_size_8_64 sz in
  let vs := (- wsigned w)%Z in
  let v := (- w)%R in
  flags_w
  [:: wsigned   v != vs; (w != 0)%R;
      SF_of_word v; PF_of_word v; ZF_of_word v ]
  v.

Definition x86_inc {sz} (w: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_aluop_nocf_w
    (w + 1)
    (wsigned w + 1)%Z.

Definition x86_dec {sz} (w: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_aluop_nocf_w
    (w - 1)
    (wsigned w - 1)%Z.

Definition x86_setcc (b:bool) : exec values := ok [:: Vword (wrepr U8 (Z.b2z b))].

Definition x86_bt {sz} (x y: word sz) : exec values :=
  Let _  := check_size_8_64 sz in
  ok [:: Vbool (wbit x y) ].

Definition x86_lea {sz} (disp base scale offset: word sz) : exec values :=
  Let _  := check_size_32_64 sz in
  if check_scale (wunsigned scale) then
    ok [::Vword (disp + base + scale * offset)]
  else type_error.

Definition x86_test {sz} (x y: word sz) : exec values :=
  Let _  := check_size_8_64 sz in
  vbools (rflags_of_bwop (wand x y)).

Definition x86_cmp {sz} (x y: word sz) :=
  Let _  := check_size_8_64 sz in
  vbools
    (rflags_of_aluop (x - y)
       (wunsigned x - wunsigned y)%Z (wsigned x - wsigned y)%Z).

Definition x86_and {sz} (v1 v2: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_bwop_w
    (wand v1 v2).

Definition x86_or {sz} (v1 v2: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_bwop_w
    (wor v1 v2).

Definition x86_xor {sz} (v1 v2: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_bwop_w
    (wxor v1 v2).

Definition x86_not {sz} (v: word sz) : exec values:=
  Let _  := check_size_8_64 sz in
  ok [:: Vword (wnot v)].

Definition x86_ror {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; Vword v]
  else
    let r := wror v (wunsigned i) in
    let CF := msb r in
    let OF :=
        if i == 1%R
        then Vbool (CF != msb v) else Vundef sbool
    in
    ok [:: OF; Vbool CF; Vword r ].

Definition x86_rol {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; Vword v]
  else
    let r := wrol v (wunsigned i) in
    let CF := lsb r in
    let OF :=
        if i == 1%R
        then Vbool (msb r != CF) else Vundef sbool
    in
    ok [:: OF; Vbool CF; Vword r ].

Definition x86_shl {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := msb (wshl v (wunsigned i - 1)) in
    let r  := wshl v (wunsigned i) in
    let OF :=
      if i == 1%R then Vbool (msb r (+) rc)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_shld {sz} (v1 v2: word sz) (i: u8) : exec values :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v1]
  else
    let rc := msb (wshl v1 (wunsigned i - 1)) in
    let r1 := wshl v1 (wunsigned i) in
    let r2 := wsar v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    let OF :=
      if i == 1%R then Vbool (msb r (+) rc)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_shr {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := lsb (wshr v (wunsigned i - 1)) in
    let r  := wshr v (wunsigned i) in

    let OF :=
      if i == 1%R then Vbool (msb r)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_shrd {sz} (v1 v2: word sz) (i: u8) : exec values :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v1]
  else
    let rc := lsb (wshr v1 (wunsigned i - 1)) in
    let r1 := wshr v1 (wunsigned i) in
    let r2 := wshl v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    let OF :=
      if i == 1%R then Vbool (msb r (+) msb v1)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_sar {sz} (v: word sz) (i: u8) : exec values :=
  Let _ := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := lsb (wsar v (wunsigned i - 1)) in
    let r  := wsar v (wunsigned i) in
    let OF :=
      if i == 1%R then Vbool false
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

(* ---------------------------------------------------------------- *)
Definition x86_bswap {sz} (v: word sz) : exec values :=
  Let _ := check_size_32_64 sz in
  ok [:: Vword (wbswap v) ].

(* ---------------------------------------------------------------- *)
Definition x86_movd {sz} (v: word sz) : exec values :=
  Let _ := check_size_32_64 sz in
  ok [:: Vword (zero_extend U128 v) ].

(* ---------------------------------------------------------------- *)
Definition x86_u128_binop sz (op: _ → _ → word sz) (v1 v2: word sz) : exec values :=
  Let _ := check_size_128_256 sz in
  ok [:: Vword (op v1 v2) ].

Definition x86_vpand {sz} := x86_u128_binop (@wand sz).
Definition x86_vpandn {sz} := x86_u128_binop (@wandn sz).
Definition x86_vpor {sz} := x86_u128_binop (@wor sz).
Definition x86_vpxor {sz} := x86_u128_binop (@wxor sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpadd (ve: velem) {sz} := x86_u128_binop (lift2_vec ve +%R sz).

Definition x86_vpmulu {sz} := x86_u128_binop (@wpmulu sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpextr (ve: wsize) (v: u128) (i: u8) :=
  (* This instruction is valid for smaller ve, but semantics is unusual,
      hence compiler correctness would not be provable. *)
  Let _ := check_size_32_64 ve in
  ok [:: Vword (nth (0%R: word ve) (split_vec ve v) (Z.to_nat (wunsigned i))) ].

(* ---------------------------------------------------------------- *)
Definition x86_vpinsr (ve: velem) (v1: u128) (v2: word ve) (i: u8) : exec values :=
  ok [:: Vword (wpinsr v1 v2 i) ].

Arguments x86_vpinsr : clear implicits.

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift sz' sz (op: word sz' → Z → word sz')
  (v: word sz) (c: u8) : exec values :=
  Let _ := check_size_16_64 sz' in
  Let _ := check_size_128_256 sz in
  ok [:: Vword (lift1_vec sz' (λ v, op v (wunsigned c)) sz v) ].

Arguments x86_u128_shift : clear implicits.

Definition x86_vpsll (ve: velem) {sz} := x86_u128_shift ve sz (@wshl _).
Definition x86_vpsrl (ve: velem) {sz} := x86_u128_shift ve sz (@wshr _).

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift_variable ve sz op v1 v2 : exec values :=
  Let _ := check_size_32_64 ve in
  Let _ := check_size_128_256 sz in
  ok [:: Vword (lift2_vec ve (λ v1 v2, op v1 (wunsigned v2)) sz v1 v2) ].

Arguments x86_u128_shift_variable : clear implicits.

Definition x86_vpsllv ve {sz} := x86_u128_shift_variable ve sz (@wshl _).
Definition x86_vpsrlv ve {sz} := x86_u128_shift_variable ve sz (@wshr _).

(* ---------------------------------------------------------------- *)
Definition x86_vpshufb {sz} := x86_u128_binop (@wpshufb sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpshuf sz (op: word sz → Z → word sz) (v1: word sz) (v2: u8) : exec values :=
  Let _ := check_size_128_256 sz in
  ok [:: Vword (op v1 (wunsigned v2)) ].

Arguments x86_vpshuf : clear implicits.

Definition x86_vpshufhw {sz} := x86_vpshuf sz (@wpshufhw _).
Definition x86_vpshuflw {sz} := x86_vpshuf sz (@wpshuflw _).
Definition x86_vpshufd {sz} := x86_vpshuf sz (@wpshufd _).

(* ---------------------------------------------------------------- *)
Definition x86_vpunpckh ve {sz} := x86_u128_binop (@wpunpckh sz ve).
Definition x86_vpunpckl ve {sz} := x86_u128_binop (@wpunpckl sz ve).

(* ---------------------------------------------------------------- *)
Definition x86_vpblendd {sz} (v1 v2: word sz) (m: u8) : exec values :=
  Let _ := check_size_128_256 sz in
  ok [:: Vword (wpblendd v1 v2 m) ].

(* ---------------------------------------------------------------- *)
Definition x86_vextracti128 (v: u256) (i: u8) : exec values :=
  let r := if lsb i then wshr v U128 else v in
  ok [:: Vword (zero_extend U128 r) ].

(* ---------------------------------------------------------------- *)
Definition x86_vperm2i128 (v1 v2: u256) (m: u8) : exec values :=
  ok [:: Vword (wperm2i128 v1 v2 m) ].

Definition x86_vpermq (v: u256) (m: u8) : exec values :=
  ok [:: Vword (wpermq v m) ].

(* ---------------------------------------------------------------- *)
Notation app_b   o := (app_sopn [:: sbool] o).
Notation app_w sz o := (app_sopn [:: sword sz] o).
Notation app_ww sz o := (app_sopn [:: sword sz; sword sz] o).
Notation app_w8 sz o := (app_sopn [:: sword sz; sword U8] o).
Notation app_www sz o := (app_sopn [:: sword sz; sword sz; sword sz] o).
Notation app_ww8 sz o := (app_sopn [:: sword sz; sword sz; sword U8] o).
Notation app_wwb sz o := (app_sopn [:: sword sz; sword sz; sbool] o).
Notation app_bww o := (app_sopn [:: sbool; sword; sword] o).
Notation app_w4 sz o  := (app_sopn [:: sword sz; sword sz; sword sz; sword sz] o).

Definition exec_sopn (o:sopn) :  values -> exec values :=
  match o with
  | Omulu sz => app_ww sz (fun x y => ok (@pval (sword sz) (sword sz) (wumul x y)))
  | Oaddcarry sz => app_wwb sz (fun x y c => ok (@pval sbool (sword sz) (waddcarry x y c)))
  | Osubcarry sz => app_wwb sz (fun x y c => ok (@pval sbool (sword sz) (wsubcarry x y c)))
  | Oset0 sz => app_sopn [::]
    (Let _ := check_size_8_64 sz in
     let vf := Vbool false in
     ok [:: vf; vf; vf; vf; Vbool true; @Vword sz 0%R])

  (* Low level x86 operations *)
  | Ox86_MOV sz => app_w sz (@x86_MOV sz)
  | Ox86_MOVSX sz sz' => app_w sz' (@x86_MOVSX sz sz')
  | Ox86_MOVZX sz sz' => app_w sz' (@x86_MOVZX sz sz')
  | Ox86_MOVZX32 => app_w U32 (λ x : u32, ok [:: Vword (zero_extend U64 x) ])
  | Ox86_CMOVcc sz => (fun v => match v with
    | [:: v1; v2; v3] =>
      Let _ := check_size_16_64 sz in
      Let b := to_bool v1 in
      if b then
        Let w2 := to_word sz v2 in ok [:: Vword w2]
      else
        Let w3 := to_word sz v3 in ok [:: Vword w3]
    | _ => type_error end)
  | Ox86_ADD sz => app_ww sz x86_add
  | Ox86_SUB sz => app_ww sz x86_sub
  | Ox86_MUL sz => app_ww sz x86_mul
  | Ox86_IMUL sz => app_ww sz x86_imul
  | Ox86_IMULt sz => app_ww sz x86_imult
  | Ox86_IMULtimm sz => app_ww sz x86_imult
  | Ox86_DIV sz => app_www sz x86_div
  | Ox86_IDIV sz => app_www sz x86_idiv
  | Ox86_CQO sz => app_w sz x86_cqo
  | Ox86_ADC sz => app_wwb sz x86_adc
  | Ox86_SBB sz => app_wwb sz x86_sbb
  | Ox86_NEG sz => app_w sz x86_neg
  | Ox86_INC sz => app_w sz x86_inc
  | Ox86_DEC sz => app_w sz x86_dec
  | Ox86_SETcc => app_b x86_setcc
  | Ox86_BT sz => app_ww sz x86_bt
  | Ox86_LEA sz => app_w4 sz x86_lea
  | Ox86_TEST sz => app_ww sz x86_test
  | Ox86_CMP sz => app_ww sz x86_cmp
  | Ox86_AND sz => app_ww sz x86_and
  | Ox86_OR sz => app_ww sz x86_or
  | Ox86_XOR sz => app_ww sz x86_xor
  | Ox86_NOT sz => app_w sz x86_not
  | Ox86_ROL sz => app_w8 sz x86_rol
  | Ox86_ROR sz => app_w8 sz x86_ror
  | Ox86_SHL sz => app_w8 sz x86_shl
  | Ox86_SHR sz => app_w8 sz x86_shr
  | Ox86_SAR sz => app_w8 sz x86_sar
  | Ox86_SHLD sz => app_ww8 sz x86_shld
  | Ox86_SHRD sz => app_ww8 sz x86_shrd
  | Ox86_BSWAP sz => app_w sz x86_bswap
  | Ox86_MOVD sz => app_w sz x86_movd
  | Ox86_VMOVDQU sz => app_sopn [:: sword sz ] (λ x,
                                                Let _ := check_size_128_256 sz in
                                                ok [:: Vword x])
  | Ox86_VPAND sz => app_ww sz x86_vpand
  | Ox86_VPANDN sz => app_ww sz x86_vpandn
  | Ox86_VPOR sz => app_ww sz x86_vpor
  | Ox86_VPXOR sz => app_ww sz x86_vpxor
  | Ox86_VPADD ve sz => app_ww sz (x86_vpadd ve)
  | Ox86_VPMULU sz => app_ww sz x86_vpmulu
  | Ox86_VPEXTR ve => app_w8 U128 (x86_vpextr ve)
  | Ox86_VPINSR ve => app_sopn [:: sword128 ; sword ve ; sword8 ] (x86_vpinsr ve)
  | Ox86_VPSLL ve sz => app_w8 sz (x86_vpsll ve)
  | Ox86_VPSRL ve sz => app_w8 sz (x86_vpsrl ve)
  | Ox86_VPSLLV ve sz => app_ww sz (x86_vpsllv ve)
  | Ox86_VPSRLV ve sz => app_ww sz (x86_vpsrlv ve)
  | Ox86_VPSHUFB sz => app_ww sz x86_vpshufb
  | Ox86_VPSHUFHW sz => app_w8 sz x86_vpshufhw
  | Ox86_VPSHUFLW sz => app_w8 sz x86_vpshuflw
  | Ox86_VPSHUFD sz => app_w8 sz x86_vpshufd
  | Ox86_VPUNPCKH ve sz => app_ww sz (x86_vpunpckh ve)
  | Ox86_VPUNPCKL ve sz => app_ww sz (x86_vpunpckl ve)
  | Ox86_VPBLENDD sz => app_ww8 sz x86_vpblendd
  | Ox86_VEXTRACTI128 => app_w8 U256 x86_vextracti128
  | Ox86_VPERM2I128 => app_ww8 U256 x86_vperm2i128
  | Ox86_VPERMQ => app_w8 U256 x86_vpermq
  end.

Ltac app_sopn_t := 
  match goal with
  | |- forall (_:wsize), _     => move=> ?;app_sopn_t
  | |- forall (_:velem), _     => move=> ?;app_sopn_t
  | |- forall (_:value), _     => move=> ?;app_sopn_t
  | |- forall (_:seq value), _ => move=> ?;app_sopn_t
  | |- (match ?vs with
       | [::] => type_error
       | _ :: _ => _ end = ok _) -> _ =>
    case: vs => // ??; app_sopn_t
  | |- ((Let _ := _ in _) = ok _) -> _ =>
    t_xrbindP => ??;app_sopn_t
  | |- (match ?vs with
       | [::] => _ 
       | _ :: _ => _ end = ok _) -> _ =>
       case: vs => //; app_sopn_t 
  | |- _ = ok ?a -> _ => move => /(@ok_inj _ _ _ _); app_sopn_t
  | |- ?a = ?b -> _ => (move => ?; subst a || subst b); app_sopn_t
  | _ => idtac
  end.

Lemma sopn_toutP o vs vs' : exec_sopn o vs = ok vs' ->
  List.map type_of_val vs' = sopn_tout o.
Proof.
  rewrite /exec_sopn ;case: o => /=; app_sopn_t => //;
  try (by apply: rbindP => _ _; app_sopn_t).
  + by move=> ?;case: ifP => ??;t_xrbindP => ?? <-.
  + by rewrite /x86_div;t_xrbindP => ??;case: ifP => // ? [<-].
  + by rewrite /x86_idiv;t_xrbindP => ??;case: ifP => // ? [<-].
  + by rewrite /x86_lea;t_xrbindP => ??;case: ifP => // ? [<-].
  + by rewrite /x86_ror;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_rol;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_shl;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_shr;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_sar;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_shld;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  by rewrite /x86_shrd;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
Qed.

Section SEM.

Variable P:prog.
Context (gd: glob_defs).

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let i1 := sem_pexpr gd s pe1 >>= to_int in
  Let i2 := sem_pexpr gd s pe2 >>= to_int in
  ok (wrange d i1 i2).

Definition sem_sopn o m lvs args :=
  sem_pexprs gd m args >>= exec_sopn o >>= write_lvals gd m lvs.

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
| Eassgn s1 s2 (x:lval) tag ty e v v':
    sem_pexpr gd s1 e = ok v ->
    truncate_val ty v = ok v' →
    write_lval gd x v' s1 = ok s2 ->
    sem_i s1 (Cassgn x tag ty e) s2

| Eopn s1 s2 t o xs es:
    sem_sopn o s1 xs es = ok s2 ->
    sem_i s1 (Copn xs t o es) s2

| Eif_true s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 s4 c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile c e c') s4 ->
    sem_i s1 (Cwhile c e c') s4

| Ewhile_false s1 s2 c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool false) ->
    sem_i s1 (Cwhile c e c') s2

| Efor s1 s2 (i:var_i) d lo hi c vlo vhi :
    sem_pexpr gd s1 lo = ok (Vint vlo) ->
    sem_pexpr gd s1 hi = ok (Vint vhi) ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    sem_i s1 (Cfor i (d, lo, hi) c) s2

| Ecall s1 m2 s2 ii xs f args vargs vs :
    sem_pexprs gd s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_lvals gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
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
| EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' :
    get_fundef P fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem s1 f.(f_body) (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    sem_call m1 fn vargs'  m2 vres'.

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

  Definition sem_Ind_nil : Prop :=
    forall s : estate, Pc s [::] s.

  Definition sem_Ind_cons : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd),
      sem_I s1 i s2 -> Pi s1 i s2 -> sem s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate),
      sem_i s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
      sem_pexpr gd s1 e = ok v ->
      truncate_val ty v = ok v' →
      write_lval gd x v' s1 = Ok error s2 ->
      Pi_r s1 (Cassgn x tag ty e) s2.

  Definition sem_Ind_opn : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
      sem_sopn o s1 xs es = Ok error s2 ->
      Pi_r s1 (Copn xs t o es) s2.

  Definition sem_Ind_if_true : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
      sem_pexpr gd s1 e = ok (Vbool true) ->
      sem s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_if_false : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
      sem_pexpr gd s1 e = ok (Vbool false) ->
      sem s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_while_true : Prop :=
    forall (s1 s2 s3 s4 : estate) (c : cmd) (e : pexpr) (c' : cmd),
      sem s1 c s2 -> Pc s1 c s2 ->
      sem_pexpr gd s2 e = ok (Vbool true) ->
      sem s2 c' s3 -> Pc s2 c' s3 ->
      sem_i s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) (c : cmd) (e : pexpr) (c' : cmd),
      sem s1 c s2 -> Pc s1 c s2 ->
      sem_pexpr gd s2 e = ok (Vbool false) ->
      Pi_r s1 (Cwhile c e c') s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_for : Prop :=
    forall (s1 s2 : estate) (i : var_i) (d : dir) (lo hi : pexpr) (c : cmd) (vlo vhi : Z),
      sem_pexpr gd s1 lo = ok (Vint vlo) ->
      sem_pexpr gd s1 hi = ok (Vint vhi) ->
      sem_for i (wrange d vlo vhi) s1 c s2 ->
      Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

  Definition sem_Ind_for_nil : Prop :=
    forall (s : estate) (i : var_i) (c : cmd),
      Pfor i [::] s c s.

  Definition sem_Ind_for_cons : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i) (w : Z) (ws : seq Z) (c : cmd),
      write_var i w s1 = Ok error s1' ->
      sem s1' c s2 -> Pc s1' c s2 ->
      sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypotheses
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .

  Definition sem_Ind_call : Prop :=
    forall (s1 : estate) (m2 : mem) (s2 : estate)
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs vs : seq value),
      sem_pexprs gd s1 args = Ok error vargs ->
      sem_call (emem s1) fn vargs m2 vs -> Pfun (emem s1) fn vargs m2 vs ->
      write_lvals gd {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
      Pi_r s1 (Ccall ii xs fn args) s2.

  Definition sem_Ind_proc : Prop :=
    forall (m1 m2 : mem) (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s1 : estate) (vm2 : vmap) (vres vres': seq value),
      get_fundef P fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem s1 (f_body f) {| emem := m2; evm := vm2 |} ->
      Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun m1 fn vargs' m2 vres'.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

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
    | @Eassgn s1 s2 x tag ty e1 v v' h1 h2 h3 => @Hasgn s1 s2 x tag ty e1 v v' h1 h2 h3
    | @Eopn s1 s2 t o xs es e1 => @Hopn s1 s2 t o xs es e1
    | @Eif_true s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c1 s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c2 s2 s0)
    | @Ewhile_true s1 s2 s3 s4 c e1 c' h1 h2 h3 h4 =>
      @Hwhile_true s1 s2 s3 s4 c e1 c' h1 (@sem_Ind s1 c s2 h1) h2 h3 (@sem_Ind s2 c' s3 h3) 
          h4 (@sem_i_Ind s3 (Cwhile c e1 c') s4 h4)
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
    | @EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' Hget Hctin Hw Hsem Hvres Hctout =>
       @Hproc m1 m2 fn f vargs vargs' s1 vm2 vres vres' Hget Hctin Hw Hsem (sem_Ind Hsem) Hvres Hctout
    end.

End SEM_IND.


Lemma of_val_undef t t':
  of_val t (Vundef t') =
    Error (if subtype t t' then ErrAddrUndef else ErrType).
Proof.
  case: t t' => //= [  [] |  [] | | s []] //.
  move=> s p [] // s' p';  case:eqP => [-> | ] /=; last by case: eqP => // -[] ->.
  case: eqP => [-> | ] //=; first by rewrite eq_refl.
  by case: eqP => // -[] ->.
Qed.

Lemma of_val_undef_ok t t' v:
  of_val t (Vundef t') <> ok v.
Proof. by rewrite of_val_undef;case:ifP. Qed.

Lemma of_varr t s n (a:Array.array n (word s)) z :
  of_val t (Varr a) = ok z -> t = sarr s n.
Proof.
  case: t z => //= s' n' z.
  case: wsize_eq_dec => // eq1.
  case: CEDecStype.pos_dec => // eq2 _.
  by congr sarr.
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

End SEM.
