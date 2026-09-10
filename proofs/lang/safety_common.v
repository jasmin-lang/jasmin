From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.
Require Import expr sopn_semi.
Import Utf8.

(* ------------------------------------------------------------------------- *)
(* Translation of a condition on the arguments of an operator into an
   expression (resp. an assertion) on the argument expressions. The coercion
   from words to integers is a parameter: [wint_int] does not need it.

   An out-of-range argument, or a condition that the defensive semantics of
   expressions does not compute (an operator outside of the [sc_total] white
   list, or an [IAppN_safety] under an operator), gives [false]: it is then
   asserted false, which is sound. *)

Section TO_E.

Context (toint : signedness -> wsize -> pexpr -> pexpr).

(* The word-to-integer coercion is used instead of [Papp1] when it is applied
   to an argument: this is what [wint_int] needs. *)
Definition sc_op1_to_e (o : sop1) (c : safe_cond) (e : pexpr) : pexpr :=
  match o, c with
  | Oint_of_word sg ws, IVar _ => toint sg ws e
  | _, _ => Papp1 o e
  end.

Fixpoint sc_to_e (vs : pexprs) (c : safe_cond) : pexpr :=
  match c with
  | IBool b => Pbool b
  | IConst z => Pconst z
  | IVar k => nth (Pbool false) vs k
  | IOp1 o c => sc_op1_to_e o c (sc_to_e vs c)
  | IOp2 o c1 c2 => Papp2 o (sc_to_e vs c1) (sc_to_e vs c2)
  | IAppN_safety _ _ => Pbool false
  end.

Definition sc_to_eassert (vs : pexprs) (c : safe_cond) : eassert :=
  match c with
  | IAppN_safety o cs =>
    if all sc_expr cs && ssrnat.leq (sc_max_var c) (size vs)
    then PappN_safety o (map (sc_to_e vs) cs)
    else Pexpr (Pbool false)
  | _ => Pexpr (if sc_expr c && ssrnat.leq (sc_max_var c) (size vs)
                then sc_to_e vs c else Pbool false)
  end.

End TO_E.

Section DEFS.
Context `{asmop:asmOp}.
Context (m: var -> option (signedness * var)).

Definition safety_cond := seq eassert.

Definition esubtype (ty1 ty2 : extended_type Z) :=
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

Fixpoint aands es :=
  match es with
  | [::] => Pexpr etrue
  | [::e] => e
  | e::es => Pand e (aands es)
  end.

Definition to_etype sg (t:atype) : extended_type Z :=
  match t with
  | abool    => tbool
  | aint     => tint
  | aarr ws l => tarr ws l
  | aword ws => ETword _ sg ws
  end.

Definition sign_of_var x := Option.map fst (m x).

Definition etype_of_var x : extended_type Z :=
  to_etype (sign_of_var x) (vtype x).

Definition sign_of_gvar (x : gvar) :=
  if is_lvar x then sign_of_var (gv x)
  else None.

Definition etype_of_gvar x := to_etype (sign_of_gvar x) (vtype (gv x)).

Definition sign_of_etype (ty: extended_type Z) : option signedness :=
  match ty with
  | ETword (Some s) _ => Some s
  | _ => None
  end.

Fixpoint etype_of_expr (e:pexpr) : extended_type Z :=
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
  end.

Definition sign_of_expr (e:pexpr) : option signedness :=
  sign_of_etype (etype_of_expr e).

(* Op1: Casts*)

Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sg sz) e.

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

Definition eis_aligned e sz := eeqi (emodi Unsigned e (ewsize sz)) (Pconst 0).

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

(* [check_xs] is generic in the language the safety conditions are written in:
   [wint_int] generates plain [pexpr]s, the safety pass generates [eassert]s.
   [read_A] and [use_mem_A] are the corresponding [read_es] / [use_mem]. *)
Section CHECK_XS.

Context {A : Type} (read_A : seq A -> Sv.t) (use_mem_A : A -> bool).

Fixpoint check_xs (okmem : bool) W xs (scs : seq (seq A)) :=
  match xs, scs with
  | [::], [::] => true
  | x :: xs, sc :: scs =>
    [&& okmem || (~~has use_mem_A sc)
      , disjoint (read_A sc) W
      & check_xs (okmem && ~~lv_write_mem x) (vrv_rec W x) xs scs]
  | _, _ => false (* Should never occurs *)
  end.

End CHECK_XS.

End DEFS.
