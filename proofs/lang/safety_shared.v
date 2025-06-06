Require Import psem.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Section DEFS.
Context `{asmop:asmOp}.

Context (m: var -> option (signedness * var)).

Definition safety_cond := seq pexpr.

Definition esubtype (ty1 ty2 : extended_type positive) :=
 match ty1, ty2 with
 | ETword None w, ETword None w' => (w ≤ w')%CMP
 | ETword (Some sg) w, ETword (Some sg') w' => (sg == sg') && (w == w')
 | ETint, ETint => true
 | ETbool, ETbool => true
 | ETarr l, ETarr l' => l == l'
 | _, _ => false
 end.

Definition etrue := Pbool true.

Fixpoint eands es :=
  match es with
  | [::] => etrue
  | [::e] => e
  | e::es => eand e (eands es)
  end.

Definition to_etype sg (t:stype) : extended_type positive:=
  match t with
  | sbool    => tbool
  | sint     => tint
  | sarr l   => tarr l
  | sword ws => ETword _ sg ws
  end.

Definition sign_of_var x := Option.map fst (m x).

Definition etype_of_var x : extended_type positive :=
  to_etype (sign_of_var x) (vtype x).

Definition sign_of_gvar (x : gvar) :=
  if is_lvar x then sign_of_var (gv x)
  else None.

Definition etype_of_gvar x := to_etype (sign_of_gvar x) (vtype (gv x)).

Definition sign_of_etype (ty: extended_type positive) : option signedness :=
  match ty with
  | ETword (Some s) _ => Some s
  | _ => None
  end.

Fixpoint etype_of_expr (e:pexpr) : extended_type positive :=
  match e with
  | Pconst _ => tint
  | Pbool _ => tbool
  | Parr_init len => tarr len
  | Pvar x => etype_of_gvar x
  | Pget al aa ws x e => tword ws
  | Psub al ws len x e => tarr (Z.to_pos (arr_size ws len))
  | Pload al ws e => tword ws
  | Papp1 o e => (etype_of_op1 o).2
  | Papp2 o e1 e2 => (etype_of_op2 o).2
  | PappN o es => to_etype None (type_of_opN o).2
  | Pif ty e1 e2 e3 => to_etype (sign_of_etype (etype_of_expr e2)) ty
  | Pbig ei o v e es el => (etype_of_op2 o).2
  | Parr_init_elem e len => tarr len
  | Pis_var_init _ => tbool
  | Pis_arr_init _ _ _ => tbool
  | Pis_barr_init _ _ _ => tbool
  | Pis_mem_init _ _ => tbool
  end.

Definition sign_of_expr (e:pexpr) : option signedness :=
  sign_of_etype (etype_of_expr e).

(* Op2: Logics *)
Definition elti e1 e2 := Papp2 (Olt Cmp_int) e1 e2.
Definition elei e1 e2 := Papp2 (Ole Cmp_int) e1 e2.
Definition eeqi e1 e2 := Papp2 (Oeq Op_int) e1 e2.
Definition eneqi e1 e2 := Papp2 (Oneq Op_int) e1 e2.
Definition elsli e1 e2 := Papp2 (Olsl Op_int) e1 e2.

(* Op2: Arithmetics *)
Definition eaddi e1 e2 := Papp2 (Oadd Op_int) e1 e2.
Definition emuli e1 e2 := Papp2 (Omul Op_int) e1 e2.
Definition emodi e1 e2 := Papp2 (Omod Unsigned Op_int) e1 e2.

(* Consts *)
Definition ezero := Pconst 0.
Definition ewsize sz := Pconst (wsize_size sz).
Definition emin_signed sz := Pconst (wmin_signed sz).
Definition emax_signed sz := Pconst (wmax_signed sz).
Definition emax_unsigned sz := Pconst (wmax_unsigned sz).

Definition emk_scale aa sz e :=
  if (aa == AAdirect) then e
  else emuli e (Pconst (wsize_size sz)).

Definition eis_aligned e sz := eeq (emodi e (ewsize sz)) (Pconst 0).

(* ------ SC_OPS ------ *)

Definition sc_in_range lo hi e := eand (elei lo e) (elei e hi).
Definition sc_uint_range sz e := sc_in_range ezero (emax_unsigned sz) e.
Definition sc_sint_range sz e := sc_in_range (emin_signed sz) (emax_signed sz) e.
Definition sc_wi_range sg sz e := signed (sc_uint_range sz) (sc_sint_range sz) sg e.

Definition is_wi1 (o: sop1) :=
  if o is Owi1 s op then Some (s, op) else None.

Definition is_wi2 (o: sop2) :=
  if o is Owi2 s sw op then Some (s, sw, op) else None.

Definition sc_wiop1 sg (o : wiop1) e :=
  match o with
  | WIwint_of_int sz => [:: sc_wi_range sg sz e]
  | WIint_of_wint sz => [::]
  | WIword_of_wint sz => [::]
  | WIwint_of_word sz => [::]
  | WIwint_ext szo szi => [::]
  | WIneg sz =>
      signed  [::eeqi e ezero ]
              [::eneqi e (emin_signed sz)] sg
  end.

(* [op : int -> int -> int] [e1 e2 : int] *)
Definition sc_wi_range_op2 sg sz op e1 e2 :=
  sc_wi_range sg sz (Papp2 op e1 e2).

(* [e1 e2 : int] *)
Definition sc_divmod sg sz e1 e2 :=
 let sc := signed [::]
                  [:: enot (eand (eeqi e1 (emin_signed sz)) (eeqi e2 (Pconst (-1)))) ] sg in
 [:: eneqi e2 ezero & sc].

Definition sc_wiop2 sg sz o e1 e2 :=
  match o with
  | WIadd => [:: sc_wi_range_op2 sg sz (Oadd Op_int) e1 e2]
  | WImul => [:: sc_wi_range_op2 sg sz (Omul Op_int) e1 e2]
  | WIsub => [:: sc_wi_range_op2 sg sz (Osub Op_int) e1 e2]
  | WIdiv => sc_divmod sg sz e1 e2
  | WImod => sc_divmod sg sz e1 e2
  | WIshl => [:: sc_wi_range sg sz (elsli e1 e2) ]
  | WIshr => [::]
  | WIeq | WIneq | WIlt | WIle | WIgt | WIge  => [::]
  end.

Definition sc_op1 (op1 : sop1) e :=
  match is_wi1 op1 with
  | Some (sg, o) => sc_wiop1 sg o e
  | None => [::]
  end.

Definition sc_op2 o e1 e2 :=
  match is_wi2 o with
  | Some (sg, sz, o) => sc_wiop2 sg sz o e1 e2
  | _ => [::]
  end.

End DEFS.

Section LEMMAS.
Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

#[local] Existing Instance nosubword.
#[local] Existing Instance withassert.

Lemma etrueE gd s : sem_cond gd etrue s = ok true.
Proof. done. Qed.

Lemma enotE gd s e b:
  sem_cond gd (enot e) s = ok b <-> sem_cond gd e s = ok (~~b).
Proof.
  rewrite /sem_cond /= /sem_sop1 /=; split; t_xrbindP.
  + by move=> > -> ? /= -> <- [<-]; rewrite Bool.negb_involutive.
  by move=> > -> /= -> /=; rewrite Bool.negb_involutive.
Qed.

Lemma eandE gd s e1 e2 :
  sem_cond gd (eand e1 e2) s = ok true <-> sem_cond gd e1 s = ok true /\ sem_cond gd e2 s = ok true.
Proof.
  rewrite /eand /sem_cond /= /sem_sop2 /=; split.
  + by t_xrbindP => > -> > -> /= b1 -> b2 -> <-; case: b1 b2 => -[].
  by move=> []; t_xrbindP => > -> /= -> > -> /= ->.
Qed.

Lemma eandsE_nil gd s : sem_cond gd (eands [::]) s = ok true.
Proof. done. Qed.

Lemma eandsE_1 gd s e : sem_cond gd (eands [::e]) s = sem_cond gd e s.
Proof. done. Qed.

Lemma eandsE_cons gd s e es :
  sem_cond gd (eands (e::es)) s = ok true <-> sem_cond gd e s = ok true /\ sem_cond gd (eands es) s = ok true.
Proof.
  rewrite /=; case: es => /=.
  + rewrite etrueE; tauto.
  by move=> ??; rewrite eandE.
Qed.

Lemma read_etrue : read_e etrue = Sv.empty.
Proof. done. Qed.

Lemma read_eands es : Sv.Equal (read_e (eands es)) (read_es es).
Proof.
  elim: es => //= e l hrec; rewrite read_es_cons -hrec => {hrec}.
  case: l.
  + rewrite /= read_etrue; SvD.fsetdec.
  move=> a l; move: (a::l) => {a} {}l.
  by rewrite read_e_Papp2.
Qed.

Lemma use_mem_eands es :
  use_mem (eands es) = has (fun e => use_mem e) es.
Proof.
  elim: es => //=.
  move=> a [ /= | a' l] hl.
  + by rewrite orbF.
  by move: (a'::l) hl => {a'} {}l <-.
Qed.

Opaque eands.

Lemma eandsE_cat gd s es1 es2 :
   sem_cond gd (eands (es1 ++ es2)) s = ok true <->
   sem_cond gd (eands es1) s = ok true /\ sem_cond gd (eands es2) s = ok true.
Proof.
  elim: es1 => //=.
  + by rewrite etrueE; tauto.
  move=> e es1 hrec; rewrite !eandsE_cons hrec; tauto.
Qed.
End LEMMAS.
