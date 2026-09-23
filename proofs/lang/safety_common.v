From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From mathcomp Require Import word_ssrZ.
Require Import expr op_semi.
Import Utf8.

(* ------------------------------------------------------------------------- *)
(* Translation of a condition on the argument values of an operator into an
   expression, and into an assertion, on its argument expressions. The
   coercion from words to integers is a parameter: [wint_int] takes the
   identity, its arguments being already integers; the safety pass applies
   [Oint_of_word].

   A variable beyond the arguments, or a predicate [IOpN_safety] below an
   operator, which the expression language cannot express, gives the assertion
   [false]: asserting it is sound. *)

Section TO_E.

Context (toint : signedness -> wsize -> pexpr -> pexpr).

(* The word-to-integer coercion is used instead of [Papp1] when it is applied
   to an argument: this is what [wint_int] needs. *)
Definition sc_op1_to_e (o : sop1) (c : safety_cond) (e : pexpr) : pexpr :=
  match o, c with
  | Oint_of_word sg ws, IVar _ => toint sg ws e
  | _, _ => Papp1 o e
  end.

Fixpoint sc_to_e (vs : pexprs) (c : safety_cond) : pexpr :=
  match c with
  | IBool b => Pbool b
  | IConst z => Pconst z
  | IVar k => nth (Pbool false) vs k
  | IOp1 o c => sc_op1_to_e o c (sc_to_e vs c)
  | IOp2 o c1 c2 => Papp2 o (sc_to_e vs c1) (sc_to_e vs c2)
  (* The predicates of the safety conditions are not expressions: they are
     assertions ([PappN_safety]), so there is nothing to translate here. *)
  | IOpN_safety _ _ _ _ => Pbool false
  end.

(* The conditions [sc_to_e] translates into an expression: those without the
   predicates [IOpN_safety]. *)
Fixpoint safety_cond_expr (c : safety_cond) : bool :=
  match c with
  | IBool _ | IConst _ | IVar _ => true
  | IOp1 _ c => safety_cond_expr c
  | IOp2 _ c1 c2 => safety_cond_expr c1 && safety_cond_expr c2
  | IOpN_safety _ _ _ _ => false
  end.

(* A predicate [IOpN_safety] at the top is the assertion [PappN_safety]. *)
Definition sc_to_eassert (vs : pexprs) (c : safety_cond) : eassert :=
  if safety_cond_below (size vs) c then
    match c with
    | IOpN_safety o c1 c2 c3 =>
      if [&& safety_cond_expr c1, safety_cond_expr c2 & safety_cond_expr c3]
      then PappN_safety o [:: sc_to_e vs c1; sc_to_e vs c2; sc_to_e vs c3]
      else Pexpr (Pbool false)
    | _ => Pexpr (if safety_cond_expr c then sc_to_e vs c else Pbool false)
    end
  else Pexpr (Pbool false).

End TO_E.

Section DEFS.
Context `{asmop:asmOp}.
Context (m: var -> option (signedness * var)).

Definition safety_asserts := seq eassert.

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

Definition safety_lbl := "safety"%string.

Definition safe_assert ii (sc:safety_asserts) : cmd :=
  map (fun e => MkI ii (Cassert (safety_lbl, e))) sc.

Definition is_wi1 (o: sop1) :=
  if o is Owi1 s op then Some (s, op) else None.

Definition is_wi2 (o: sop2) :=
  if o is Owi2 s sw op then Some (s, sw, op) else None.

(* The assertions attached to an assignment are checked before it, so they
   must not read what it writes. *)
Fixpoint check_xs (okmem : bool) W xs (scs : seq safety_asserts) :=
  match xs, scs with
  | [::], [::] => true
  | x :: xs, sc :: scs =>
    [&& okmem || (~~has use_mem_eassert sc)
      , disjoint (read_easserts sc) W
      & check_xs (okmem && ~~lv_write_mem x) (vrv_rec W x) xs scs]
  | _, _ => false (* Should never occurs *)
  end.

End DEFS.
