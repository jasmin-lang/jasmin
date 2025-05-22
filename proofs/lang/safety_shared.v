From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.
Require Import expr.
Import Utf8.

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
 | ETarr ws l, ETarr ws' l' => arr_size ws l == arr_size ws' l'
 | _, _ => false
 end.

Definition etrue := Pbool true.

Fixpoint eands es :=
  match es with
  | [::] => etrue
  | [::e] => e
  | e::es => eand e (eands es)
  end.

Definition to_etype sg (t:atype) : extended_type positive:=
  match t with
  | abool    => tbool
  | aint     => tint
  | aarr ws l => tarr ws l
  | aword ws => ETword _ sg ws
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
  | Parr_init ws len => tarr ws len
  | Pvar x => etype_of_gvar x
  | Pget al aa ws x e => tword ws
  | Psub al ws len x e => tarr ws len
  | Pload al ws e => tword ws
  | Papp1 o e => (etype_of_op1 o).2
  | Papp2 o e1 e2 => (etype_of_op2 o).2
  | PappN o es => to_etype None (type_of_opN o).2
  | Pif ty e1 e2 e3 => to_etype (sign_of_etype (etype_of_expr e2)) ty
  | Pbig ei o v e es el => (etype_of_op2 o).2
  | Pis_var_init _ => tbool
  | Pis_mem_init _ _ => tbool
  end.

Definition sign_of_expr (e:pexpr) : option signedness :=
  sign_of_etype (etype_of_expr e).

(* Op1: Casts*)

Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sg sz) e.
Definition word_of_int (sg:signedness) sz i := Papp1 (Oword_of_int sz) (Pconst i).

(* Op2: Logics *)
Definition elti e1 e2 := Papp2 (Olt Cmp_int) e1 e2.
Definition elei e1 e2 := Papp2 (Ole Cmp_int) e1 e2.
Definition eeqi e1 e2 := Papp2 (Oeq Op_int) e1 e2.
Definition eneqi e1 e2 := Papp2 (Oneq Op_int) e1 e2.
Definition elsli e1 e2 := Papp2 (Olsl Op_int) e1 e2.

(* Op2: Arithmetics *)
Definition eaddi e1 e2 := Papp2 (Oadd Op_int) e1 e2.
Definition emuli e1 e2 := Papp2 (Omul Op_int) e1 e2.
Definition edivi sg e1 e2 := Papp2 (Odiv sg Op_int) e1 e2.
Definition emodi sg e1 e2 := Papp2 (Omod sg Op_int) e1 e2.

(* Consts *)
Definition ezero := Pconst 0.
Definition ewsize sz := Pconst (wsize_size sz).
Definition emin_signed sz := Pconst (wmin_signed sz).
Definition emax_signed sz := Pconst (wmax_signed sz).
Definition emax_unsigned sz := Pconst (wmax_unsigned sz).

Definition emk_scale aa sz e :=
  if (aa == AAdirect) then e
  else emuli e (Pconst (wsize_size sz)).

Definition eis_aligned e sz := eeq (emodi Unsigned e (ewsize sz)) (Pconst 0).

Definition safety_lbl := "safety"%string.

Definition safe_assert ii (sc:safety_cond) : cmd :=
  map (fun e => MkI ii (Cassert (safety_lbl, e))) sc.

(* ------ SC_OPS ------ *)

Definition sc_in_range lo hi e := eand (elei lo e) (elei e hi).
Definition sc_uint_range sz e := sc_in_range ezero (emax_unsigned sz) e.
Definition sc_sint_range sz e := sc_in_range (emin_signed sz) (emax_signed sz) e.
Definition sc_wi_range sg sz e := signed (sc_uint_range sz) (sc_sint_range sz) sg e.

Definition is_wi1 (o: sop1) :=
  if o is Owi1 s op then Some (s, op) else None.

Definition is_wi2 (o: sop2) :=
  if o is Owi2 s sw op then Some (s, sw, op) else None.

Definition sc_wiop1 (toint : signedness -> wsize -> pexpr -> pexpr)
  sg (o : wiop1) (e: pexpr) :=
  match o with
  | WIwint_of_int sz => [:: sc_wi_range sg sz e]
  | WIint_of_wint sz => [::]
  | WIword_of_wint sz => [::]
  | WIwint_of_word sz => [::]
  | WIwint_ext szo szi => [::]
  | WIneg sz =>
      signed  [::eeqi (toint sg sz e) ezero ]
              [::eneqi (toint sg sz e) (emin_signed sz)] sg
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

Definition sc_op1 (toint : signedness -> wsize -> pexpr -> pexpr)
  (op1 : sop1) e :=
  match is_wi1 op1 with
  | Some (sg, o) => sc_wiop1 toint sg o e
  | None => [::]
  end.  

Fixpoint get_var_contract (v: var_i) (vs: seq var_i) (vs': seq var_i) : option var_i :=
    match vs, vs' with
      | x::vs, x'::vs' =>
        if var_beq v x then Some x' else get_var_contract v vs vs'
      | _, _ => None
    end.
    
Definition sc_all cond v start len :=
  if cond is nil then [::]
  else [:: Pbig etrue Oand v (eands cond) start len].

Fixpoint check_xs (okmem : bool) W xs scs :=
  match xs, scs with
  | [::], [::] => true
  | x :: xs, sc :: scs =>
    [&& okmem || (~~has (fun e => use_mem e) sc)
      , disjoint (read_es sc) W
      & check_xs (okmem && ~~lv_write_mem x) (vrv_rec W x) xs scs]
  | _, _ => false (* Should never occurs *)
  end.

End DEFS.
