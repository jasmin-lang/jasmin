(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import Psatz xseq.
Require Export array type expr gen_map low_memory warray_ sem_type values.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition zlsl (x i : Z) : Z :=
  if (0 <=? i)%Z then (x * 2^i)%Z
  else (x / 2^(-i))%Z.

Definition zasr (x i : Z) : Z := 
  zlsl x (-i).

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
  | Obeq => mk_sem_sop2 (@eq_op [eqType of bool])
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

Definition neg_f (n:bool) (f:bool) := 
  if n then ~~f else f.

Definition sem_cfc (n:bool) (o:combine_flags_core) (OF CF SF ZF : bool) : exec bool := 
  let r :=
    match o with
    | CFC_O => OF
    | CFC_B => CF
    | CFC_E => ZF
    | CFC_S => SF
    | CFC_L => OF!=SF
    | CFC_BE => CF || ZF
    | CFC_LE => (OF!=SF) || ZF
    end in
  ok (neg_f n r).

Definition sem_combine_flags (o:combine_flags) : 
  sem_prod tin_combine_flags (exec bool) := 
    let c := cf_tbl o in
    sem_cfc c.1 c.2.

Definition sem_opN_typed (o: opN) :
  let t := type_of_opN o in
  sem_prod t.1 (exec (sem_t t.2)) :=
  match o with
  | Opack sz pe => curry (A := sint) (sz %/ pe) (λ vs, ok (wpack sz pe vs))
  | Ocombine_flags o => sem_combine_flags o  
  end.

Definition sem_opN (op: opN) (vs: values) : exec value :=
  Let w := app_sopn _ (sem_opN_typed op) vs in
  ok (to_val w).

Record estate {pd: PointerData} := Estate {
  emem : mem;
  evm  : vmap
}.

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

Definition get_global_value (gd: glob_decls) (g: var) : option glob_value :=
  assoc gd g.

Definition gv2val (gd:glob_value) := 
  match gd with
  | Gword ws w => Vword w
  | Garr p a   => Varr a 
  end.

Definition get_global gd g : exec value :=
  if get_global_value gd g is Some ga then
    let v := gv2val ga in
    if type_of_val v == vtype g then ok v
    else type_error
  else type_error.

Lemma get_globalI gd g v :
  get_global gd g = ok v →
  exists gv : glob_value, [/\ get_global_value gd g = Some gv, v = gv2val gv & type_of_val v = vtype g].
Proof.
  rewrite /get_global; case: get_global_value => // gv.
  by case:eqP => // <- [<-];exists gv.
Qed.

Definition get_gvar (gd: glob_decls) (vm: vmap) (x:gvar) :=
  if is_lvar x then get_var vm x.(gv)
  else get_global gd x.(gv).

Definition on_arr_var A (v:exec value) (f:forall n, WArray.array n -> exec A) :=
  Let v := v  in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

Notation "'Let' ( n , t ) ':=' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

Lemma type_of_get_var x vm v :
  get_var vm x = ok v ->
  type_of_val v = x.(vtype).
Proof. by rewrite /get_var; apply : on_vuP => // t _ <-; apply type_of_to_val. Qed.

Lemma on_arr_varP
  {pd: PointerData} A (f : forall n, WArray.array n -> exec A) v s x P :
  (forall n t, vtype x = sarr n ->
               get_var (evm s) x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var (get_var (evm s) x) f = ok v -> P.
Proof.
  rewrite /on_arr_var=> H;apply: rbindP => vx hx.
  have h := type_of_get_var hx; case: vx h hx => // len t h.
  by apply: H;rewrite -h.
Qed.

Lemma type_of_get_global gd g v :
  get_global gd g = ok v -> type_of_val v = vtype g. 
Proof. by move=> /get_globalI [?[]]. Qed.

Lemma type_of_get_gvar x gd vm v :
  get_gvar gd vm x = ok v ->
  type_of_val v = vtype x.(gv).
Proof. 
  rewrite /get_gvar;case:ifP => ?.
  + by apply type_of_get_var.
  by apply type_of_get_global.
Qed.

Lemma on_arr_gvarP A (f : forall n, WArray.array n -> exec A) v gd s x P:
  (forall n t, vtype x.(gv) = sarr n ->
               get_gvar gd s x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var (get_gvar gd s x) f = ok v -> P.
Proof.
  rewrite /on_arr_var=> H;apply: rbindP => vx hx.
  have h := type_of_get_gvar hx; case: vx h hx => // len t h.
  by apply: H;rewrite -h.
Qed.

Definition is_defined (v: value) : bool :=
  if v is Vundef _ _ then false else true.

Section SEM_PEXPR.

Context {pd: PointerData}.
Context (gd: glob_decls).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Parr_init n => ok (Varr (WArray.empty n))
  | Pvar v => get_gvar gd s.(evm) v
  | Pget aa ws x e =>
      Let (n, t) := gd, s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := WArray.get aa ws t i in
      ok (Vword w)
  | Psub aa ws len x e =>
      Let (n, t) := gd, s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let t' := WArray.get_sub aa ws len t i in
      ok (Varr t')
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := read s.(emem) (w1 + w2)%R sz in
    ok (@to_val (sword sz) w)
  | Papp1 o e1 =>
    Let v1 := sem_pexpr s e1 in
    sem_sop1 o v1
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    sem_sop2 o v1 v2
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    sem_opN op vs
  | Pif t e e1 e2 =>
    Let b := sem_pexpr s e >>= to_bool in
    Let v1 := sem_pexpr s e1 >>= truncate_val t in
    Let v2 := sem_pexpr s e2 >>= truncate_val t in
    ok (if b then v1 else v2)
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok ({| emem := s.(emem); evm := vm |}).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s:estate) ty v :=
  on_vu (fun v => s) (if is_sbool ty then ok s else type_error)
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
    Let m :=  write s.(emem) p w in
    ok {| emem := m;  evm := s.(evm) |}
  | Laset aa ws x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := WArray.set t aa i v in
    write_var x (@to_val (sarr n) t) s
  | Lasub aa ws len x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (Z.to_pos (arr_size ws len)) v in 
    Let t := @WArray.set_sub n aa ws len t i t' in
    write_var x (@to_val (sarr n) t) s
  end.

Definition write_lvals (s:estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.


(* ---------------------------------------------------------------- *)
Definition is_word (sz: wsize) (v: value) : exec unit :=
  match v with
  | Vword _ _ | Vundef (sword _) _ => ok tt
  | _ => type_error end.

Lemma is_wordI sz v u :
  is_word sz v = ok u →
  subtype (vundef_type (sword sz)) (type_of_val v).
Proof. case: v => // [ sz' w | [] // ] _; exact: wsize_le_U8. Qed.

(* ---------------------------------------------------------------- *)

Section ASM_OP.

Context `{asmop:asmOp}.

Definition exec_sopn (o:sopn) (vs:values) : exec values :=
  let semi := sopn_sem o in
  Let t := app_sopn _ semi vs in
  ok (list_ltuple t).

Lemma sopn_toutP o vs vs' : exec_sopn o vs = ok vs' ->
  List.map type_of_val vs' = sopn_tout o.
Proof.
  rewrite /exec_sopn /sopn_tout /sopn_sem.
  t_xrbindP => p _ <-;apply type_of_val_ltuple.
Qed.

Section SEM.

Context {pd: PointerData}.

Variable P:uprog.

Notation gd := (p_globs P).

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let i1 := sem_pexpr gd s pe1 >>= to_int in
  Let i2 := sem_pexpr gd s pe2 >>= to_int in
  ok (wrange d i1 i2).

Definition sem_sopn gd o m lvs args :=
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
    sem_sopn gd o s1 xs es = ok s2 ->
    sem_i s1 (Copn xs t o es) s2

| Eif_true s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 s4 a c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile a c e c') s4 ->
    sem_i s1 (Cwhile a c e c') s4

| Ewhile_false s1 s2 a c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool false) ->
    sem_i s1 (Cwhile a c e c') s2

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
    get_fundef (p_funcs P) fn = Some f ->
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
      sem_sopn gd o s1 xs es = Ok error s2 ->
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
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
      sem s1 c s2 -> Pc s1 c s2 ->
      sem_pexpr gd s2 e = ok (Vbool true) ->
      sem s2 c' s3 -> Pc s2 c' s3 ->
      sem_i s3 (Cwhile a c e c') s4 -> Pi_r s3 (Cwhile a c e c') s4 -> Pi_r s1 (Cwhile a c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
      sem s1 c s2 -> Pc s1 c s2 ->
      sem_pexpr gd s2 e = ok (Vbool false) ->
      Pi_r s1 (Cwhile a c e c') s2.

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
      get_fundef (p_funcs P) fn = Some f ->
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
    | @Ewhile_true s1 s2 s3 s4 a c e1 c' h1 h2 h3 h4 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 c' h1 (@sem_Ind s1 c s2 h1) h2 h3 (@sem_Ind s2 c' s3 h3) 
          h4 (@sem_i_Ind s3 (Cwhile a c e1 c') s4 h4)
    | @Ewhile_false s1 s2 a c e1 c' s0 e2 =>
      @Hwhile_false s1 s2 a c e1 c' s0 (@sem_Ind s1 c s2 s0) e2
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

Lemma of_val_undef t t' hn:
  of_val t (Vundef t' hn) =
    Error (if subtype t t' then ErrAddrUndef else ErrType).
Proof. by case: t t' hn => //= [ | | p | s] []. Qed.

Lemma of_val_undef_ok t t' hn v:
  of_val t (Vundef t' hn) <> ok v.
Proof. by rewrite of_val_undef. Qed.

Lemma of_varr t n (a:WArray.array n) z :
  of_val t (Varr a) = ok z -> subtype t (sarr n).
Proof.
  by case: t z => //= n' z; rewrite /WArray.cast; case: ifP.
Qed.

Lemma of_vword t s (w: word s) z :
  of_val t (Vword w) = ok z -> exists s', (s' <= s)%CMP /\ t = sword s'.
Proof.
  case: t z => //= s' w' H.
  exists s';split => //=.
  by move: H; rewrite /truncate_word;  case: (s' <= s)%CMP => //=.
Qed.

Lemma of_vint t n z :
  of_val t (Vint n) = ok z -> t = sint.
Proof.
  case: t z => //= s' w'.
Qed.

Lemma of_vbool ty b v :
  of_val ty (Vbool b) = ok v → ∃ e : ty = sbool, ecast ty (sem_t ty) e v = b.
Proof. by case: ty v => // _ /ok_inj <-; exists erefl. Qed.

End SEM.

End ASM_OP.
