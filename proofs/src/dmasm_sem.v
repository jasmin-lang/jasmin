(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
Require Import choice fintype eqtype div seq finmap strings zmodp.
Require Import dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Local Scope ring_scope.

(* ** Types for idents and values
 * -------------------------------------------------------------------- *)

Definition ident := string.

Parameter wsize : nat.

Definition bword := (2^wsize)%N.

Definition word := 'Z_bword.

Definition n2w (n : nat) : word := n%:R.

Definition w2n (w : word) : nat := w%N.

(* ** Source language types
 * -------------------------------------------------------------------- *)

Inductive stype :=
| Tword : stype
| Tarr  : stype
| Tbool : stype.

Definition stype_eqMixin := comparableClass (@LEM stype).
Canonical  stype_eqType  := Eval hnf in EqType stype stype_eqMixin.

(* ** Arrays
 * -------------------------------------------------------------------- *)

Local Open Scope fmap.

Definition arr := {fmap word -> word}.

(* ** Source language values
 * -------------------------------------------------------------------- *)

Inductive sval := 
| Varr  : arr  -> sval
| Vbool : bool -> sval
| Vword : word -> sval.

Definition sval_eqMixin := comparableClass (@LEM sval).
Canonical  sval_eqType  := Eval hnf in EqType sval sval_eqMixin.

Definition stype_of_sval (v : sval) :=
  match v with
  | Varr  _ => Tarr
  | Vword _ => Tword
  | Vbool _ => Tbool
  end.

Definition type_of_stype (t : stype) : Type :=
  match t with
  | Tarr  => arr
  | Tword => word
  | Tbool => bool
  end.

Definition get_vword (v : sval) :=
  match v with
  | Vword w => Some w
  | _       => None
  end.

Definition get_varr (v : sval) :=
  match v with
  | Varr a => Some a
  | _      => None
  end.

Definition get_vbool (v : sval) :=
  match v with
  | Vbool b => Some b
  | _       => None
  end.

(* ** Function-local variable map
 * -------------------------------------------------------------------- *)

Definition lmap := {fmap ident -> sval}.

(* ** Parameter expressions and conditions
 * -------------------------------------------------------------------- *)

Inductive pop_word :=
| Padd
| Pmul
| Psub.

Definition eval_pop_word (o : pop_word) : (word -> word -> word) :=
  match o with
  | Padd => fun x y => x + y
  | Psub => fun x y => x - y
  | Pmul => fun x y => x * y
  end.

Inductive pexpr :=
| Pvar   : ident -> pexpr
| Pbinop : pop_word -> pexpr -> pexpr -> pexpr
| Pconst : word -> pexpr.

Fixpoint eval_pexpr (lm : lmap) pe :=
  match pe with
  | Pvar id          => obind get_vword lm.[? id]
  | Pconst w         => Some w
  | Pbinop pw pe1 pe2 =>
      eval_pexpr lm pe1 >>= fun w1 =>
      eval_pexpr lm pe2 >>= fun w2 =>
      Some ((eval_pop_word pw) w1 w2)
  end.

Inductive pop_bool :=
| Peq
| Pineq
| Pless
| Pleq
| Pgreater
| Pgeq.

Definition eval_pop_bool (o : pop_bool) : (word -> word -> bool) :=
  match o with
  | Peq      => fun w1 w2 => w1 == w2
  | Pineq    => fun w1 w2 => w1 != w2
  | Pless    => fun w1 w2 => w1 < w2
  | Pleq     => fun w1 w2 => w1 <= w2
  | Pgreater => fun w1 w2 => w1 > w2
  | Pgeq     => fun w1 w2 => w1 >= w2
  end.

Inductive pcond :=
| Ptrue
| Pnot  : pcond -> pcond
| Pand  : pcond -> pcond -> pcond
| Pcond : pop_bool -> pexpr -> pexpr -> pcond.

Fixpoint eval_pcond lm pc :=
  match pc with
  | Ptrue    =>
      Some true
  | Pnot pc  =>
      eval_pcond lm pc >>= fun b =>
      Some (~~ b)
  | Pand pc1 pc2 =>
      eval_pcond lm pc1 >>= fun b1 =>
      eval_pcond lm pc2 >>= fun b2 =>
      Some (b1 && b2)
  | Pcond po pe1 pe2 =>
      eval_pexpr lm pe1 >>= fun w1 =>
      eval_pexpr lm pe2 >>= fun w2 =>
      Some ((eval_pop_bool po) w1 w2)
  end.

(* ** Operators
 * -------------------------------------------------------------------- *)

Inductive op :=
| Move : op
| Add  : bool -> op (* Add true => return carry *)
| Addc : bool -> op (* Addc true => return carry *)
| Cmov_eq_to : bool -> op.

Definition op_eqMixin := comparableClass (@LEM op).
Canonical  op_eqType  := Eval hnf in EqType op op_eqMixin.

Definition addc_n (w1 w2 : word) (cf : bool) :=
  w1%N + w2%N + cf%:R.

Definition addc_w (w1 w2 : word) (cf : bool) : word :=
  nosimpl (addc_n w1 w2 cf).

Definition addc_cf (w1 w2 : word) (cf : bool) : bool :=
  nosimpl (addc_n w1 w2 cf < bword).

Definition addc (w1 w2 : word) (cf : bool) : bool * word :=
  (addc_cf w1 w2 cf, addc_w w1 w2 cf).

Definition add_w (w1 w2 : word) : word :=
  nosimpl (addc_w w1 w2 false).

Definition add_cf (w1 w2 : word) : bool :=
  nosimpl (addc_cf w1 w2 false).

Definition add (w1 w2 : word) : bool * word :=
  (add_cf w1 w2, add_w w1 w2).

Definition eval_op op (args : seq sval) : option (seq sval) :=
  match op, args with
  | Move, _ =>
      Some args
  | Addc c, [:: Vword w1; Vword w2; Vbool cf ] =>
      let (cf,w) := addc w1 w2 cf in
      let cf := if c then [:: Vbool cf ] else [::] in
      Some (cf ++ [:: Vword w ])
  | Addc _, _ =>
      None
  | Add c,  [:: Vword w1; Vword w2 ] =>
      let (cf,w) := add w1 w2 in
      let cf := if c then [:: Vbool cf ] else [::] in
      Some (cf ++ [:: Vword w ])
  | Add _, _ =>
      None
  | Cmov_eq_to f, [:: Vword w1; Vword w2; Vbool b ] =>
      Some [:: Vword (if (b == f) then w1 else w2) ]
  | Cmov_eq_to _, _ =>
      None
  end.

(* ** Locations and sources
 * -------------------------------------------------------------------- *)

Record loc := mkLoc {
  l_oidx : option pexpr;
  l_id   : ident
}.

Definition loc_eqMixin := comparableClass (@LEM loc).
Canonical  loc_eqType  := Eval hnf in EqType loc loc_eqMixin.

Inductive src : Type :=
| Imm : pexpr -> src
| Loc : loc  -> src.

(* ** Reading local variables
 * -------------------------------------------------------------------- *)

Definition read_oidx lm (oidx : option pexpr) (v : sval) : option sval :=
  match oidx, v with
  | None   ,_        => Some v
  | Some(_),Vword(_) => None
  | Some(_),Vbool(_) => None
  | Some(pe),Varr(a)  =>
      eval_pexpr lm pe >>= fun w =>
      omap Vword a.[? w]
  end.

Definition read_loc (lm : lmap) (l : loc) : option sval :=
  lm.[? l.(l_id)] >>= fun v =>
                        read_oidx lm l.(l_oidx) v.

Definition read_src (lm : lmap) (s : src) : option sval :=
  match s with
  | Imm pe => eval_pexpr lm pe >>= fun w => Some (Vword w)
  | Loc d  => read_loc lm d
  end.

Definition read_ty ty (s : src) (lm : lmap) : option (type_of_stype ty) :=
  match read_src lm s, ty with
  | Some (Vword w), Tword => Some w
  | Some (Varr a),  Tarr  => Some a
  | _            ,_       => None
  end.

(* ** Writing local variables
 * -------------------------------------------------------------------- *)

Definition write_loc (lm : lmap) (l : loc) (v : sval) : option lmap :=
  match l.(l_oidx), v with
  | None, _ =>
      Some lm.[ l.(l_id) <- v]
  | Some pe, Vword w =>
      let ao :=
        match read_loc lm l with
        | Some (Varr a)  => Some a
        | Some (Vword _) => None (* no strong update *)
        | Some (Vbool _) => None
        | None           => Some fmap0
        end
      in
      ao >>= fun a =>
      eval_pexpr lm pe >>= fun wi =>
      Some lm.[ l.(l_id) <- Varr a.[ wi <- w] ]
  | Some _, Varr _ =>
      None
  | Some _, Vbool _ =>
      None
  end.

Fixpoint write_locs (lm : lmap) (ds : seq loc) (vs : seq sval) : option lmap :=
  match ds, vs with
  | [::], [::] => Some lm
  | [::], _    => None
  | _,    [::] => None
  | [:: d & ds], [:: v & vs] =>
      write_loc lm d v >>= fun lm =>
      write_locs lm ds vs
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Inductive instr :=
| Skip
| Seq   : instr -> instr -> instr
| Assgn : seq loc -> op -> seq src -> instr 
| If    : pcond -> instr -> instr -> instr
| For   : ident -> pexpr -> pexpr -> instr -> instr
| Call  : (seq ident *  seq src * instr) (* function def: (args, body, ret) *)
          -> seq ident
          -> seq src
          -> instr.

Fixpoint eval_instr (lm : lmap) (i : instr) : option lmap :=
  match i with
  | Skip =>
      Some lm

  | Seq i1 i2 =>
      eval_instr lm i1 >>= fun lm =>
      eval_instr lm i2

  | Assgn ds op ss =>
      mapM (read_src lm) ss >>= fun args =>
      eval_op op args >>= fun res =>
      write_locs lm ds res

  | If pc i1 i2 =>
      eval_pcond lm pc >>= fun cond =>
      if cond then eval_instr lm i1 else eval_instr lm i2

  | For id lb_pe ub_pe i => (* FIXME: support decreasing loop *)
      let step :=
        fun j lm =>
          eval_instr lm.[ id <- Vword j] i
      in
      eval_pexpr lm lb_pe >>= fun lb =>
      eval_pexpr lm ub_pe >>= fun ub =>
      foldM step lm (map (fun n => n2w n) (list_from_to (w2n lb) (w2n ub)))

  | Call fd drets args =>
      let: (fargs,frets,fbody) := fd in
      (* read values for given args *)
      mapM (read_src lm) args >>= fun args =>
      (* write given args as formal args into fresh stack frame *)
      write_locs fmap0 (map (mkLoc None) fargs) args >>= fun lm_call =>
      (* evaluate body *)
      eval_instr lm_call fbody >>= fun lm_call =>
      (* read return values *)
      mapM (read_src lm_call) frets >>= fun rets =>
      (* store return values into dret *)
      write_locs fmap0 (map (mkLoc None) drets) rets

  end.