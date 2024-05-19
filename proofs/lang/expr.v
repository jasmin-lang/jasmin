(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg.
Require Import oseq.
Require Export ZArith Setoid Morphisms.
From mathcomp Require Import word_ssrZ.
Require Export strings word utils type ident var global sem_type slh_ops sopn syscall.
Require Import xseq.
Import Utf8 ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

(* ** Operators
 * -------------------------------------------------------------------- *)
(* *** Summary
   Operators represent several constructs in the Ocaml compiler:
   - const-op: compile-time expressions (constexpr in C++)
   - list-op: argument and result lists
   - arr-op: reading and writing arrays
   - cpu-op: CPU instructions such as addition with carry
*)

Variant cmp_kind :=
  | Cmp_int
  | Cmp_w of signedness & wsize.

Variant op_kind :=
  | Op_int
  | Op_w of wsize.

Variant sop1 :=
| Oword_of_int of wsize     (* int → word *)
| Oint_of_word of wsize     (* word → unsigned int *)
| Osignext of wsize & wsize (* Sign-extension: output-size, input-size *)
| Ozeroext of wsize & wsize (* Zero-extension: output-size, input-size *)
| Onot                      (* Boolean negation *)
| Olnot of wsize            (* Bitwize not: 1s’ complement *)
| Oneg  of op_kind          (* Arithmetic negation *)
.

Variant sop2 :=
| Obeq                        (* const : sbool -> sbool -> sbool *)
| Oand                        (* const : sbool -> sbool -> sbool *)
| Oor                         (* const : sbool -> sbool -> sbool *)

| Oadd  of op_kind
| Omul  of op_kind
| Osub  of op_kind
| Odiv  of cmp_kind
| Omod  of cmp_kind

| Oland of wsize
| Olor  of wsize
| Olxor of wsize
| Olsr  of wsize 
| Olsl  of op_kind
| Oasr  of op_kind
| Oror  of wsize
| Orol  of wsize

| Oeq   of op_kind
| Oneq  of op_kind
| Olt   of cmp_kind
| Ole   of cmp_kind
| Ogt   of cmp_kind
| Oge   of cmp_kind

(* vector operation *)
| Ovadd of velem & wsize (* VPADD   *)
| Ovsub of velem & wsize (* VPSUB   *)
| Ovmul of velem & wsize (* VPMULLW *)
| Ovlsr of velem & wsize
| Ovlsl of velem & wsize
| Ovasr of velem & wsize
.

(* N-ary operators *)
Variant combine_flags :=
| CF_LT    of signedness   (* Alias : signed => L  ; unsigned => B   *) 
| CF_LE    of signedness   (* Alias : signed => LE ; unsigned => BE  *)
| CF_EQ                    (* Alias : E                              *)
| CF_NEQ                   (* Alias : !E                             *)
| CF_GE    of signedness   (* Alias : signed => !L ; unsigned => !B  *)
| CF_GT    of signedness   (* Alias : signed => !LE; unsigned => !BE *)
.

Variant opN :=
| Opack of wsize & pelem (* Pack words of size pelem into one word of wsize *)
| Ocombine_flags of combine_flags
.

Scheme Equality for sop1.
(* Definition sop1_beq : sop1 -> sop1 -> bool *)

Lemma sop1_eq_axiom : Equality.axiom sop1_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_sop1_dec_bl internal_sop1_dec_lb).
Qed.

Definition sop1_eqMixin     := Equality.Mixin sop1_eq_axiom.
Canonical  sop1_eqType      := Eval hnf in EqType sop1 sop1_eqMixin.

Scheme Equality for sop2.
(* Definition sop2_beq : sop2 -> sop2 -> bool *)

Lemma sop2_eq_axiom : Equality.axiom sop2_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_sop2_dec_bl internal_sop2_dec_lb).
Qed.

Definition sop2_eqMixin     := Equality.Mixin sop2_eq_axiom.
Canonical  sop2_eqType      := Eval hnf in EqType sop2 sop2_eqMixin.

Scheme Equality for opN.

Lemma opN_eq_axiom : Equality.axiom opN_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_opN_dec_bl internal_opN_dec_lb).
Qed.

Definition opN_eqMixin     := Equality.Mixin opN_eq_axiom.
Canonical  opN_eqType      := Eval hnf in EqType opN opN_eqMixin.

(* ----------------------------------------------------------------------------- *)

(* Type of unany operators: input, output *)
Definition type_of_op1 (o: sop1) : stype * stype :=
  match o with
  | Oword_of_int sz => (sint, sword sz)
  | Oint_of_word sz => (sword sz, sint)
  | Osignext szo szi
  | Ozeroext szo szi
    => (sword szi, sword szo)
  | Onot => (sbool, sbool)
  | Olnot sz
  | Oneg (Op_w sz)
    => let t := sword sz in (t, t)
  | Oneg Op_int => (sint, sint)
  end.

(* Type of binany operators: inputs, output *)
Definition type_of_op2 (o: sop2) : stype * stype * stype :=
  match o with
  | Obeq | Oand | Oor => (sbool, sbool, sbool)
  | Oadd Op_int
  | Omul Op_int
  | Osub Op_int
  | Odiv Cmp_int | Omod Cmp_int
  | Olsl Op_int | Oasr Op_int
    => (sint, sint, sint)
  | Oadd (Op_w s)
  | Omul (Op_w s)
  | Osub (Op_w s)
  | Odiv (Cmp_w _ s) | Omod (Cmp_w _ s)
  | Oland s | Olor s | Olxor s | Ovadd _ s | Ovsub _ s | Ovmul _ s
    => let t := sword s in (t, t, t)
  | Olsr s | Olsl (Op_w s) | Oasr (Op_w s) | Oror s | Orol s
  | Ovlsr _ s | Ovlsl _ s | Ovasr _ s
    => let t := sword s in (t, sword8, t)
  | Oeq Op_int | Oneq Op_int
  | Olt Cmp_int | Ole Cmp_int
  | Ogt Cmp_int | Oge Cmp_int
    => (sint, sint, sbool)
  | Oeq (Op_w s) | Oneq (Op_w s)
  | Olt (Cmp_w _ s) | Ole (Cmp_w _ s)
  | Ogt (Cmp_w _ s) | Oge (Cmp_w _ s)
    => let t := sword s in (t, t, sbool)
  end.

(* Type of n-ary operators: inputs, output *)

Definition tin_combine_flags := [:: sbool; sbool; sbool; sbool].

Definition type_of_opN (op: opN) : seq stype * stype :=
  match op with
  | Opack ws p =>
    let n := nat_of_wsize ws %/ nat_of_pelem p in
    (nseq n sint, sword ws)
  | Ocombine_flags c => (tin_combine_flags, sbool) 
  end.

(* ** Expressions
 * -------------------------------------------------------------------- *)
(* Used only by the ocaml compiler *)
(** A “tag” is a non-empty type, extracted to plain OCaml [int] *)
Module Type TAG.
  Parameter t : Type.
  Parameter witness : t.
End TAG.

Module VarInfo : TAG.
  Definition t := positive.
  Definition witness : t := 1%positive.
End VarInfo.

Definition var_info := VarInfo.t.
Definition dummy_var_info : var_info := VarInfo.witness.

Record var_i := VarI {
  v_var :> var;
  v_info : var_info
}.

Definition mk_var_i (x : var) :=
  {|
    v_var := x;
    v_info := dummy_var_info;
  |}.

Notation vid ident :=
  (mk_var_i {| vtype := sword Uptr; vname := ident%string; |}).

Variant v_scope := 
  | Slocal 
  | Sglob.

Scheme Equality for v_scope.

Lemma v_scope_eq_axiom : Equality.axiom v_scope_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_v_scope_dec_bl internal_v_scope_dec_lb).
Qed.

Definition v_scope_eqMixin     := Equality.Mixin v_scope_eq_axiom.
Canonical  v_scope_eqType      := Eval hnf in EqType v_scope v_scope_eqMixin.

Record gvar := Gvar { gv : var_i; gs : v_scope }.

Definition mk_gvar x := {| gv := x; gs := Sglob  |}.
Definition mk_lvar x := {| gv := x; gs := Slocal |}.

Definition is_lvar (x:gvar) := x.(gs) == Slocal.
Definition is_glob (x:gvar) := x.(gs) == Sglob.

Inductive pexpr : Type :=
| Pconst :> Z -> pexpr
| Pbool  :> bool -> pexpr
| Parr_init : positive → pexpr
| Pvar   :> gvar -> pexpr
| Pget   : aligned -> arr_access -> wsize -> gvar -> pexpr -> pexpr
| Psub   : arr_access -> wsize -> positive -> gvar -> pexpr -> pexpr
| Pload  : aligned -> wsize -> var_i -> pexpr -> pexpr
| Papp1  : sop1 -> pexpr -> pexpr
| Papp2  : sop2 -> pexpr -> pexpr -> pexpr
| PappN of opN & seq pexpr
| Pif    : stype -> pexpr -> pexpr -> pexpr -> pexpr.

Notation pexprs := (seq pexpr).

Definition Plvar x := Pvar (mk_lvar x).

Definition enot e := Papp1 Onot e.
Definition eor e1 e2 := Papp2 Oor e1 e2.
Definition eand e1 e2 := Papp2 Oand e1 e2.
Definition eeq e1 e2 := Papp2 Obeq e1 e2.
Definition eneq e1 e2 := enot (eeq e1 e2).

Definition cf_of_condition (op : sop2) : option (combine_flags * wsize) :=
  match op with
  | Oeq (Op_w ws) => Some (CF_EQ, ws)
  | Oneq (Op_w ws) => Some (CF_NEQ, ws)
  | Olt (Cmp_w s ws) => Some (CF_LT s, ws)
  | Ole (Cmp_w s ws) => Some (CF_LE s, ws)
  | Ogt (Cmp_w s ws) => Some (CF_GT s, ws)
  | Oge (Cmp_w s ws) => Some (CF_GE s, ws)
  | _ => None
  end.

Definition pexpr_of_cf (cf : combine_flags) (vi : var_info) (flags : seq var) : pexpr :=
  let eflags := [seq Plvar {| v_var := x; v_info := vi |} | x <- flags ] in
  PappN (Ocombine_flags cf) eflags.


(* ** Left values
 * -------------------------------------------------------------------- *)

Variant lval : Type :=
| Lnone `(var_info) `(stype)
| Lvar  `(var_i)
| Lmem  of aligned & wsize & var_i & pexpr
| Laset of aligned & arr_access & wsize & var_i & pexpr
| Lasub `(arr_access) `(wsize) `(positive) `(var_i) `(pexpr).

Coercion Lvar : var_i >-> lval.

Notation lvals := (seq lval).

Definition get_pvar (e: pexpr) : exec var :=
  if e is Pvar {| gv := x ; gs := Slocal |} then ok (v_var x) else type_error.

Definition get_lvar (x: lval) : exec var :=
  if x is Lvar x then ok (v_var x) else type_error.

Definition Lnone_b (vi : var_info) : lval := Lnone vi sbool.

Definition var_info_of_lval (x: lval) : var_info :=
  match x with
  | Lnone i t => i
  | Lvar x | Lmem _ _ x _ | Laset _ _ _ x _ | Lasub _ _ _ x _ => v_info x
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Variant dir := UpTo | DownTo.

Scheme Equality for dir.

Lemma dir_eq_axiom : Equality.axiom dir_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_dir_dec_bl internal_dir_dec_lb).
Qed.

Definition dir_eqMixin     := Equality.Mixin dir_eq_axiom.
Canonical  dir_eqType      := Eval hnf in EqType dir dir_eqMixin.

Definition range := (dir * pexpr * pexpr)%type.

Definition wrange d (n1 n2 : Z) :=
  let n := Z.to_nat (n2 - n1) in
  match d with
  | UpTo   => [seq (Z.add n1 (Z.of_nat i)) | i <- iota 0 n]
  | DownTo => [seq (Z.sub n2 (Z.of_nat i)) | i <- iota 0 n]
  end.

Module Type InstrInfoT <: TAG.
  Include TAG.
  Parameter with_location : t -> t.
  Parameter is_inline : t -> bool.
  Parameter var_info_of_ii : t -> var_info.
End InstrInfoT.

Module InstrInfo : InstrInfoT.
  Definition t := positive.
  Definition witness : t := 1%positive.
  Definition with_location (ii : t) := ii.
  Definition is_inline (_ : t) : bool := false.
  Definition var_info_of_ii (_ : t) : var_info := dummy_var_info.
End InstrInfo.

Definition instr_info := InstrInfo.t.
Definition dummy_instr_info : instr_info := InstrInfo.witness.
Definition ii_with_location (ii : instr_info) : instr_info :=
  InstrInfo.with_location ii.
Definition ii_is_inline (ii : instr_info) : bool := InstrInfo.is_inline ii.
Definition var_info_of_ii (ii : instr_info) : var_info := InstrInfo.var_info_of_ii ii.

Variant assgn_tag :=
  | AT_none       (* assignment introduced by the developer that can be removed *)
  | AT_keep       (* assignment that should be kept by the compiler *)
  | AT_rename     (* equality constraint introduced by inline, used in reg-alloc
                     and compiled to no-op *)
  | AT_inline     (* assignment to be propagated and removed later : introduced
                     by unrolling, inlining or lowering *)
  | AT_phinode    (* renaming during SSA transformation *)
  .

Scheme Equality for assgn_tag.

Lemma assgn_tag_eq_axiom : Equality.axiom assgn_tag_beq.
Proof.
  exact:
    (eq_axiom_of_scheme internal_assgn_tag_dec_bl internal_assgn_tag_dec_lb).
Qed.

Definition assgn_tag_eqMixin     := Equality.Mixin assgn_tag_eq_axiom.
Canonical  assgn_tag_eqType      := Eval hnf in EqType assgn_tag assgn_tag_eqMixin.

(* -------------------------------------------------------------------- *)

Variant align :=
  | Align
  | NoAlign.

(* -------------------------------------------------------------------- *)

Section ASM_OP.

Context `{asmop:asmOp}.

Inductive instr_r :=
| Cassgn   : lval -> assgn_tag -> stype -> pexpr -> instr_r
| Copn     : lvals -> assgn_tag -> sopn -> pexprs -> instr_r
| Csyscall : lvals -> syscall_t -> pexprs -> instr_r 
| Cif      : pexpr -> seq instr -> seq instr  -> instr_r
| Cfor     : var_i -> range -> seq instr -> instr_r
| Cwhile   : align -> seq instr -> pexpr -> seq instr -> instr_r
| Ccall    : lvals -> funname -> pexprs -> instr_r

with instr := MkI : instr_info -> instr_r ->  instr.

End ASM_OP.

Notation cmd := (seq instr).

Section CMD_RECT.

  Context `{asmop:asmOp}.

  Variables (Pr:instr_r -> Type) (Pi:instr -> Type) (Pc : cmd -> Type).
  Hypothesis Hmk  : forall i ii, Pr i -> Pi (MkI ii i).
  Hypothesis Hnil : Pc [::].
  Hypothesis Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hasgn: forall x tg ty e, Pr (Cassgn x tg ty e).
  Hypothesis Hopn : forall xs t o es, Pr (Copn xs t o es).
  Hypothesis Hsyscall : forall xs o es, Pr (Csyscall xs o es).
  Hypothesis Hif  : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Hypothesis Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Hypothesis Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Hypothesis Hcall: forall xs f es, Pr (Ccall xs f es).

  Section C.
  Variable instr_rect : forall i, Pi i.

  Fixpoint cmd_rect_aux (c:cmd) : Pc c :=
    match c return Pc c with
    | [::] => Hnil
    | i::c => @Hcons i c (instr_rect i) (cmd_rect_aux c)
    end.
  End C.

  Fixpoint instr_Rect (i:instr) : Pi i :=
    match i return Pi i with
    | MkI ii i => @Hmk i ii (instr_r_Rect i)
    end
  with instr_r_Rect (i:instr_r) : Pr i :=
    match i return Pr i with
    | Cassgn x tg ty e => Hasgn x tg ty e
    | Copn xs t o es => Hopn xs t o es
    | Csyscall xs o es => Hsyscall xs o es
    | Cif e c1 c2  => @Hif e c1 c2 (cmd_rect_aux instr_Rect c1) (cmd_rect_aux instr_Rect c2)
    | Cfor i (dir,lo,hi) c => @Hfor i dir lo hi c (cmd_rect_aux instr_Rect c)
    | Cwhile a c e c'   => @Hwhile a c e c' (cmd_rect_aux instr_Rect c) (cmd_rect_aux instr_Rect c')
    | Ccall xs f es => @Hcall xs f es
    end.

  Definition cmd_rect := cmd_rect_aux instr_Rect.

End CMD_RECT.

Module FunInfo : TAG.
  Definition t := positive.
  Definition witness : t := 1%positive.
End FunInfo.

Section ASM_OP.

Context `{asmop:asmOp}.

(* ** Functions
 * -------------------------------------------------------------------- *)

Definition fun_info := FunInfo.t.

Class progT := {
  extra_fun_t : Type;
  extra_prog_t : Type;
  extra_val_t  : Type;
}.

Record _fundef (extra_fun_t: Type) := MkFun {
  f_info   : fun_info;
  f_tyin   : seq stype;
  f_params : seq var_i;
  f_body   : cmd;
  f_tyout  : seq stype;
  f_res    : seq var_i;
  f_extra  : extra_fun_t;
}.

Definition _fun_decl (extra_fun_t: Type) := (funname * _fundef extra_fun_t)%type.

Record _prog (extra_fun_t: Type) (extra_prog_t: Type):= {
  p_funcs : seq (_fun_decl extra_fun_t);
  p_globs : glob_decls;
  p_extra : extra_prog_t;
}.

Section PROG.

Context {pT: progT}.

Definition fundef := _fundef extra_fun_t.

Definition function_signature : Type :=
  (seq stype * seq stype).

Definition signature_of_fundef (fd: fundef) : function_signature :=
  (f_tyin fd, f_tyout fd).

Definition fun_decl := (funname * fundef)%type.

Definition prog := _prog extra_fun_t extra_prog_t.

Definition Build_prog p_funcs p_globs p_extra : prog := Build__prog p_funcs p_globs p_extra.

End PROG.

End ASM_OP.

Notation fun_decls  := (seq fun_decl).

Section ASM_OP.

Context {pd: PointerData}.
Context `{asmop:asmOp}.

(* ** Programs before stack/memory allocation 
 * -------------------------------------------------------------------- *)

Definition progUnit : progT :=
  {| extra_fun_t := unit;
     extra_val_t := unit;
     extra_prog_t := unit;
  |}.

Definition ufundef     := @fundef _ _ progUnit.
Definition ufun_decl   := @fun_decl _ _ progUnit.
Definition ufun_decls  := seq (@fun_decl _ _ progUnit).
Definition uprog       := @prog _ _ progUnit.

(* For extraction *)
Definition _ufundef    := _fundef unit.
Definition _ufun_decl  := _fun_decl unit.
Definition _ufun_decls :=  seq (_fun_decl unit).
Definition _uprog      := _prog unit unit.
Definition to_uprog (p:_uprog) : uprog := p.

(* ** Programs after stack/memory allocation 
 * -------------------------------------------------------------------- *)

Variant saved_stack :=
| SavedStackNone
| SavedStackReg of var
| SavedStackStk of Z.

Definition saved_stack_beq (x y : saved_stack) :=
  match x, y with
  | SavedStackNone, SavedStackNone => true
  | SavedStackReg v1, SavedStackReg v2 => v1 == v2
  | SavedStackStk z1, SavedStackStk z2 => z1 == z2
  | _, _ => false
  end.

Lemma saved_stack_eq_axiom : Equality.axiom saved_stack_beq.
Proof.
  move=> [ | v1 | z1] [ | v2 | z2] /=; try by constructor.
  + by apply (iffP eqP); congruence.
  by apply (iffP eqP); congruence.
Qed.

Definition saved_stack_eqMixin   := Equality.Mixin saved_stack_eq_axiom.
Canonical  saved_stack_eqType    := Eval hnf in EqType saved_stack saved_stack_eqMixin.

Variant return_address_location :=
| RAnone
| RAreg of var & option var  (* The return address is pass by a register and
                                keeped in this register during function call,
                                the option is for incrementing the large stack in arm *)
| RAstack of option var & Z & option var.
                             (* None means that the call instruction directly store ra on the stack
                                Some r means that the call instruction directly store ra on r and 
                                the function should store r on the stack,
                                The second option is for incrementing the large stack in arm *)

Definition is_RAnone ra :=
  if ra is RAnone then true else false.

Definition is_RAstack ra :=
  if ra is RAstack _ _ _ then true else false.

Definition is_RAstack_None ra :=
  if ra is RAstack None _ _ then true else false.

Definition return_address_location_beq (r1 r2: return_address_location) : bool :=
  match r1 with
  | RAnone => if r2 is RAnone then true else false
  | RAreg x1 o1 => if r2 is RAreg x2 o2 then (x1 == x2) && (o1 == o2) else false
  | RAstack lr1 z1 o1 => if r2 is RAstack lr2 z2 o2 then [&& lr1 == lr2, z1 == z2 & o1 == o2] else false
  end.

Lemma return_address_location_eq_axiom : Equality.axiom return_address_location_beq.
Proof.
  case => [ | x1 o1 | lr1 z1 o1 ] [ | x2 o2 | lr2 z2 o2 ] /=; try by constructor.
  + by apply (iffP andP) => [ []/eqP-> /eqP-> | []-> ->].
  by apply (iffP and3P) => [ []/eqP-> /eqP-> /eqP-> | []-> -> ->].
Qed.

Definition return_address_location_eqMixin := Equality.Mixin return_address_location_eq_axiom.
Canonical  return_address_location_eqType  := Eval hnf in EqType return_address_location return_address_location_eqMixin.

Record stk_fun_extra := MkSFun {
  sf_align          : wsize;
  sf_stk_sz         : Z;
  sf_stk_ioff       : Z;
  sf_stk_extra_sz   : Z;
  sf_stk_max        : Z;
  sf_max_call_depth : Z;
  sf_to_save        : seq (var * Z);
  sf_save_stack     : saved_stack;
  sf_return_address : return_address_location;
  sf_align_args     : seq wsize;
}.

Record sprog_extra := {
  sp_rsp   : Ident.ident;
  sp_rip   : Ident.ident;
  sp_globs : seq u8;
  sp_glob_names: seq (var * wsize * Z);
}.

Definition progStack : progT :=
  {| extra_fun_t := stk_fun_extra;
     extra_val_t := pointer;
     extra_prog_t := sprog_extra  |}.

Definition sfundef     := @fundef _ _ progStack.
Definition sfun_decl   := @fun_decl _ _ progStack.
Definition sfun_decls  := seq (@fun_decl _ _ progStack).
Definition sprog       := @prog _ _ progStack.

(* For extraction *)

Definition _sfundef    := _fundef stk_fun_extra.
Definition _sfun_decl  := _fun_decl stk_fun_extra.
Definition _sfun_decls := seq (_fun_decl stk_fun_extra).
Definition _sprog      := _prog stk_fun_extra sprog_extra.
Definition to_sprog (p:_sprog) : sprog := p.

(* Update functions *)
Definition with_body eft (fd:_fundef eft) body := {|
  f_info   := fd.(f_info);
  f_tyin   := fd.(f_tyin);
  f_params := fd.(f_params);
  f_body   := body;
  f_tyout  := fd.(f_tyout);
  f_res    := fd.(f_res);
  f_extra  := fd.(f_extra);
|}.

Definition swith_extra {_: PointerData} (fd:ufundef) f_extra : sfundef := {|
  f_info   := fd.(f_info);
  f_tyin   := fd.(f_tyin);
  f_params := fd.(f_params);
  f_body   := fd.(f_body);
  f_tyout  := fd.(f_tyout);
  f_res    := fd.(f_res);
  f_extra  := f_extra;
|}.

End ASM_OP.

Section ASM_OP.

Context `{asmop:asmOp}.
Context {pT: progT}.

(* ** Some smart constructors
 * -------------------------------------------------------------------------- *)

Definition is_const (e:pexpr) :=
  match e with
  | Pconst n => Some n
  | _        => None
  end.

Definition is_bool (e:pexpr) :=
  match e with
  | Pbool b => Some b
  | _ => None
  end.

Definition is_Papp2 (e : pexpr) : option (sop2 * pexpr * pexpr) :=
  if e is Papp2 op e0 e1 then Some (op, e0, e1) else None.

Definition is_array_init e :=
  match e with
  | Parr_init _ => true
  | _           => false
  end.

Fixpoint cast_w ws (e: pexpr) : pexpr :=
  match e with
  | Papp2 (Oadd Op_int) e1 e2 =>
      let: e1 := cast_w ws e1 in
      let: e2 := cast_w ws e2 in
      Papp2 (Oadd (Op_w ws)) e1 e2
  | Papp2 (Osub Op_int) e1 e2 =>
      let: e1 := cast_w ws e1 in
      let: e2 := cast_w ws e2 in
      Papp2 (Osub (Op_w ws)) e1 e2
  | Papp2 (Omul Op_int) e1 e2 =>
      let: e1 := cast_w ws e1 in
      let: e2 := cast_w ws e2 in
      Papp2 (Omul (Op_w ws)) e1 e2
  | Papp1 (Oneg Op_int) e' =>
      let: e' := cast_w ws e' in
      Papp1 (Oneg (Op_w ws)) e'
  | Papp1 (Oint_of_word ws') e' =>
      if (ws ≤ ws')%CMP then e'
      else Papp1 (Oword_of_int ws) e
  | _ => Papp1 (Oword_of_int ws) e
  end.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Definition cast_ptr := cast_w Uptr.

Definition cast_const z := cast_ptr (Pconst z).

End WITH_POINTER_DATA.

Definition eword_of_int (ws : wsize) (x : Z) : pexpr :=
  Papp1 (Oword_of_int ws) (Pconst x).

Definition wconst (sz: wsize) (n: word sz) : pexpr :=
  Papp1 (Oword_of_int sz) (Pconst (wunsigned n)).

Definition is_wconst (sz: wsize) (e: pexpr) : option (word sz) :=
  match e with
  | Papp1 (Oword_of_int sz') e =>
    if (sz ≤ sz')%CMP then
      is_const e >>= λ n, Some (wrepr sz n)
    else None
  | _       => None
  end%O.

Definition is_wconst_of_size sz (e: pexpr) : option Z :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    if sz' == sz then Some z else None
  | _ => None end.

(* ** Compute written variables
 * -------------------------------------------------------------------- *)

Definition vrv_rec (s:Sv.t) (rv:lval) :=
  match rv with
  | Lnone _ _  => s
  | Lvar  x    => Sv.add x s
  | Lmem _ _ _ _  => s
  | Laset _ _ _ x _  => Sv.add x s
  | Lasub _ _ _ x _ => Sv.add x s
  end.

Definition vrvs_rec s (rv:lvals) := foldl vrv_rec s rv.

Definition vrv := (vrv_rec Sv.empty).
Definition vrvs := (vrvs_rec Sv.empty).

Definition lv_write_mem (r:lval) : bool :=
  if r is Lmem _ _ _ _ then true else false.

Fixpoint write_i_rec s (i:instr_r) :=
  match i with
  | Cassgn x _ _ _  => vrv_rec s x
  | Copn xs _ _ _   => vrvs_rec s xs
  | Csyscall xs _ _ => vrvs_rec s xs 
  | Cif   _ c1 c2   => foldl write_I_rec (foldl write_I_rec s c2) c1
  | Cfor  x _ c     => foldl write_I_rec (Sv.add x s) c
  | Cwhile _ c _ c' => foldl write_I_rec (foldl write_I_rec s c') c
  | Ccall x _ _   => vrvs_rec s x
  end
with write_I_rec s i :=
  match i with
  | MkI _ i => write_i_rec s i
  end.

Definition write_i i := write_i_rec Sv.empty i.

Definition write_I i := write_I_rec Sv.empty i.

Definition write_c_rec s c := foldl write_I_rec s c.

Definition write_c c := write_c_rec Sv.empty c.

(* ** Expression depends/reads on memory
 * -------------------------------------------------------------------- *)

Fixpoint use_mem (e : pexpr) :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ | Pvar _ => false
  | Pload _ _ _ _ => true
  | Pget _ _ _ _ e | Psub _ _ _ _ e | Papp1 _ e => use_mem e
  | Papp2 _ e1 e2 => use_mem e1 || use_mem e2
  | PappN _ es => has use_mem es
  | Pif _ e e1 e2 => use_mem e || use_mem e1 || use_mem e2
  end.

(* ** Compute read variables
 * -------------------------------------------------------------------- *)

Definition read_gvar (x:gvar) := 
  if is_lvar x then Sv.singleton x.(gv)
  else Sv.empty.

Fixpoint read_e_rec (s:Sv.t) (e:pexpr) : Sv.t :=
  match e with
  | Pconst _
  | Pbool  _
  | Parr_init _    => s
  | Pvar   x       => Sv.union (read_gvar x) s
  | Pget _ _ _ x e   => read_e_rec (Sv.union (read_gvar x) s) e
  | Psub _ _ _ x e => read_e_rec (Sv.union (read_gvar x) s) e
  | Pload _ _ x e  => read_e_rec (Sv.add x s) e
  | Papp1  _ e     => read_e_rec s e
  | Papp2  _ e1 e2 => read_e_rec (read_e_rec s e2) e1
  | PappN _ es     => foldl read_e_rec s es
  | Pif  _ t e1 e2 => read_e_rec (read_e_rec (read_e_rec s e2) e1) t
  end.

Definition read_e := read_e_rec Sv.empty.
Definition read_es_rec := foldl read_e_rec.
Definition read_es := read_es_rec Sv.empty.

Definition read_rv_rec  (s:Sv.t) (r:lval) :=
  match r with
  | Lnone _ _     => s
  | Lvar  _       => s
  | Lmem _ _ x e  => read_e_rec (Sv.add x s) e
  | Laset _ _ _ x e => read_e_rec (Sv.add x s) e
  | Lasub _ _ _ x e => read_e_rec (Sv.add x s) e
  end.

Definition read_rv := read_rv_rec Sv.empty.
Definition read_rvs_rec := foldl read_rv_rec.
Definition read_rvs := read_rvs_rec Sv.empty.

Fixpoint read_i_rec (s:Sv.t) (i:instr_r) : Sv.t :=
  match i with
  | Cassgn x _ _ e => read_rv_rec (read_e_rec s e) x
  | Copn xs _ _ es => read_es_rec (read_rvs_rec s xs) es
  | Csyscall xs _ es => read_es_rec (read_rvs_rec s xs) es
  | Cif b c1 c2 =>
    let s := foldl read_I_rec s c1 in
    let s := foldl read_I_rec s c2 in
    read_e_rec s b
  | Cfor x (dir, e1, e2) c =>
    let s := foldl read_I_rec s c in
    read_e_rec (read_e_rec s e2) e1
  | Cwhile a c e c' =>
    let s := foldl read_I_rec s c in
    let s := foldl read_I_rec s c' in
    read_e_rec s e
  | Ccall xs _ es => read_es_rec (read_rvs_rec s xs) es
  end
with read_I_rec (s:Sv.t) (i:instr) : Sv.t :=
  match i with
  | MkI _ i => read_i_rec s i
  end.

Definition read_c_rec := foldl read_I_rec.

Definition read_i := read_i_rec Sv.empty.

Definition read_I := read_I_rec Sv.empty.

Definition read_c := read_c_rec Sv.empty.

(* ** Compute occurring variables (= read + write)
 * -------------------------------------------------------------------------- *)

Definition vars_I (i: instr) := Sv.union (read_I i) (write_I i).

Definition vars_c c := Sv.union (read_c c) (write_c c).

Definition vars_lval l := Sv.union (read_rv l) (vrv l).

Definition vars_lvals ls := Sv.union (read_rvs ls) (vrvs ls).

Fixpoint vars_l (l: seq var_i) :=
  match l with
  | [::] => Sv.empty
  | h :: q => Sv.add h (vars_l q)
  end.

Definition vars_fd (fd:fundef) :=
  Sv.union (vars_l fd.(f_params)) (Sv.union (vars_l fd.(f_res)) (vars_c fd.(f_body))).

Definition vars_p (p: fun_decls) :=
  foldr (fun f x => let '(fn, fd) := f in Sv.union x (vars_fd fd)) Sv.empty p.

End ASM_OP.

(* --------------------------------------------------------------------- *)
(* Test the equality of two expressions modulo variable info             *)

Definition eq_gvar x x' := 
  (x.(gs) == x'.(gs)) && (v_var x.(gv) == v_var x'.(gv)).

Fixpoint eq_expr e e' :=
  match e, e' with
  | Pconst z      , Pconst z'         => z == z'
  | Pbool  b      , Pbool  b'         => b == b'
  | Parr_init n   , Parr_init n'      => n == n'
  | Pvar   x      , Pvar   x'         => eq_gvar x x'
  | Pget al aa w x e , Pget al' aa' w' x' e' => (al == al') && (aa==aa') && (w == w') && (eq_gvar x x') && eq_expr e e'
  | Psub aa w len x e , Psub aa' w' len' x' e' => (aa==aa') && (w == w') && (len == len') && (eq_gvar x x') && eq_expr e e'
  | Pload al w x e, Pload al' w' x' e' => (al == al') && (w == w') && (v_var x == v_var x') && eq_expr e e'
  | Papp1  o e    , Papp1  o' e'      => (o == o') && eq_expr e e'
  | Papp2  o e1 e2, Papp2  o' e1' e2' => (o == o') && eq_expr e1 e1' && eq_expr e2 e2'
  | PappN o es, PappN o' es' => (o == o') && (all2 eq_expr es es')
  | Pif t e e1 e2, Pif t' e' e1' e2' =>
    (t == t') && eq_expr e e' && eq_expr e1 e1' && eq_expr e2 e2'
  | _             , _                 => false
  end.

(* ------------------------------------------------------------------- *)
Definition to_lvals (l:seq var) : seq lval := 
  map (fun x => Lvar (mk_var_i x)) l.

(* ------------------------------------------------------------------- *)
Definition is_false (e: pexpr) : bool :=
  if e is Pbool false then true else false.

Definition is_zero sz (e: pexpr) : bool :=
  if e is Papp1 (Oword_of_int sz') (Pconst Z0) then sz' == sz else false.

Notation copn_args := (seq lval * sopn * seq pexpr)%type (only parsing).

Definition instr_of_copn_args
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (tg : assgn_tag)
  (args : copn_args)
  : instr_r :=
  Copn args.1.1 tg args.1.2 args.2.
