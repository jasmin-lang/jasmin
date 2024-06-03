Require Import ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import expr fexpr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

(* ** Compiler warning
 * -------------------------------------------------------------------------- *)

Variant warning_msg : Set :=
  | Use_lea.

(* ** Compiler error
 * -------------------------------------------------------------------------- *)

Variant box := 
  | Vbox
  | Hbox
  | HoVbox
  | Nobox.

Inductive pp_error :=
  | PPEstring  `(string)
  | PPEz       `(Z)
  | PPEvar     `(var)
  | PPEvarinfo    `(var_info)
(*   | PPEop1     `(sop1) *)
(*   | PPEop2     `(sop2) *)
(*   | PPEopN     `(opN) *)
(*   | PPEsopn    `(sopn) *)
(*   | PPEexpr    `(pexpr) *)
  | PPElval  of lval
  | PPEfunname `(funname)
  | PPEfuninfo `(fun_info)
(*   | PPEinstr   `(instr_r) *)
  | PPEiinfo   `(instr_info)
  | PPEexpr    `(pexpr)
  | PPErexpr of rexpr
  | PPEfexpr of fexpr
  | PPEbox     `(box) `(seq pp_error)
  | PPEbreak.

(* TODO: it was simpler to put pel_fn and pel_fi as separate fields; in the future,
   do we want to merge them?
*)
Record pp_error_loc := {
  pel_msg      : pp_error;
  pel_fn       : option funname;
  pel_fi       : option fun_info;
  pel_ii       : option instr_info;
  pel_vi       : option var_info;
  pel_pass     : option string;
  pel_internal : bool
}.

Definition pp_hov  := PPEbox HoVbox.
Definition pp_box  := PPEbox Hbox.
Definition pp_vbox := PPEbox Vbox.
Definition pp_nobox := PPEbox Nobox.

Notation pp_s    := PPEstring.
Notation pp_z    := PPEz.
Notation pp_var  := PPEvar.
Notation pp_e    := PPEexpr.
Notation pp_re   := PPErexpr.
Notation pp_fe   := PPEfexpr.
Notation pp_fn   := PPEfunname.
Notation pp_lv   := PPElval.

Fixpoint pp_list {A} sep (pp : A -> pp_error) xs : pp_error :=
  match xs with
  | [::] => pp_nobox [::]
  | [:: x] => pp x
  | x :: xs => pp_nobox [:: pp x; sep; pp_list sep pp xs]
  end.

Definition pp_break pp := pp_nobox [:: pp; PPEbreak].

Definition pp_break_s s := pp_break (pp_s s).

Definition pp_Sv (s:Sv.t) : pp_error :=
 pp_nobox [:: pp_s "{"; pp_list (pp_break_s ",") pp_var (Sv.elements s); pp_s "}"].


(* Not currently used *)
Definition pp_neq {A:Type} (pp_a: A -> pp_error) e1 e2 (_: unit):=
  pp_hov [:: pp_a e1; pp_s "should be equal to"; pp_a e2].


Definition cexec A := result pp_error_loc A.

(* -------------------------------------------------------- *)
(* Some helper functions                                    *)

Definition pp_at_ii ii (e : pp_error_loc) := {|
  pel_msg := e.(pel_msg);
  pel_fn := e.(pel_fn);
  pel_fi := e.(pel_fi);
  pel_ii := Some ii;
  pel_vi := e.(pel_vi);
  pel_pass := e.(pel_pass);
  pel_internal := e.(pel_internal) |}.

Definition add_iinfo {T} (ii:instr_info) (x : cexec T) := 
  match x with
  | Ok a => ok a 
  | Error e => Error (pp_at_ii ii e)
  end.

Definition pp_at_fi fi (e : pp_error_loc) := {|
  pel_msg := e.(pel_msg);
  pel_fn := e.(pel_fn);
  pel_fi := Some fi;
  pel_ii := e.(pel_ii);
  pel_vi := e.(pel_vi);
  pel_pass := e.(pel_pass);
  pel_internal := e.(pel_internal) |}.

Definition add_finfo {A} fi (r:cexec A) : cexec A :=
  match r with
  | Ok a => @Ok _ A a
  | Error pp => Error (pp_at_fi fi pp)
  end.

Definition pp_at_fn fn (e : pp_error_loc) := {|
  pel_msg := e.(pel_msg);
  pel_fn := Some fn;
  pel_fi := e.(pel_fi);
  pel_ii := e.(pel_ii);
  pel_vi := e.(pel_vi);
  pel_pass := e.(pel_pass);
  pel_internal := e.(pel_internal) |}.

Definition add_funname {A} fn (r:cexec A) : cexec A :=
  match r with
  | Ok a => @Ok _ A a
  | Error pp => Error (pp_at_fn fn pp)
  end.

Lemma add_iinfoP {A a} ii (e:cexec A):
  add_iinfo ii e = ok a -> 
  e = ok a.
Proof. by case: e. Qed.

Lemma add_finfoP {A a} fi (e:cexec A):
  add_finfo fi e = ok a -> 
  e = ok a.
Proof. by case: e. Qed.

Lemma add_funnameP {A a} fn (e:cexec A):
  add_funname fn e = ok a -> 
  e = ok a.
Proof. by case: e. Qed.

(* -------------------------------------------------------- *)
(* map functions on prog that preserve function names       *)

(* Used in most of the passes since they deal with each function separately *)

(* If function [F] cannot fail, we simply call it on each program function *)

Section ASM_OP.

Context `{asmop:asmOp}.
Context {pT: progT}.

Definition map_prog_name (F: funname -> fundef -> fundef) (p:prog) :prog :=
  {| p_funcs := map (fun f => (f.1, F f.1 f.2)) (p_funcs p);
     p_globs := p_globs p;
     p_extra := p_extra p|}.

Definition map_prog (F: fundef -> fundef) (p:prog) :=
  map_prog_name (fun _ => F) p.

Lemma get_map_prog_name F p fn :
  get_fundef (p_funcs (map_prog_name F p)) fn =
  ssrfun.omap (F fn) (get_fundef (p_funcs p) fn).
Proof.
  rewrite /get_fundef /map_prog_name /=.
  by elim: p_funcs => // -[fn' fd] pfuns /= ->;case:eqP => [-> | ].
Qed.

Lemma get_map_prog F p fn :
  get_fundef (p_funcs (map_prog F p)) fn = ssrfun.omap F (get_fundef (p_funcs p) fn).
Proof. apply: get_map_prog_name. Qed.

End ASM_OP.

(* If function [F] can fail, we add the function name and the function info to
   the error message potentially produced. *)

(* In general, [T1] is instantiated as [_fundef ?eft], so we can use [f_info].
   But we also instantiate [T1] as [lfundef] (in x86_gen.v), and in this case we
   need to use [lfd_info].
   We take as an argument a fonction to access the [fun_info] so that both cases
   are covered.
*)
Definition map_cfprog_name_gen {T1 T2} (info: T1 -> fun_info) (F: funname -> T1 -> cexec T2) :=
  mapM (fun (f:funname * T1) => Let x := add_finfo (info f.2) (add_funname f.1 (F f.1 f.2)) in ok (f.1, x)).

Definition map_cfprog_gen {T1 T2} (info : T1 -> fun_info) (F: T1 -> cexec T2) :=
  map_cfprog_name_gen info (fun _ t1 => F t1).

(* Some notations to use in the common case where we manipulate [_fundef ?eft]. *)
Notation map_cfprog_name := (map_cfprog_name_gen (@f_info _ _ _)).
Notation map_cfprog := (map_cfprog_gen (@f_info _ _ _)).

Lemma get_map_cfprog_name_gen {T1 T2} (info : T1 -> fun_info) (F: funname -> T1 -> cexec T2) p p' fn f:
  map_cfprog_name_gen info F p = ok p' ->
  get_fundef p fn = Some f ->
  exists2 f', F fn f = ok f' & get_fundef p' fn = Some f'.
Proof.
  move=> Hmap H.
  have [|f' /= hF hf'] := mapM_assoc _ Hmap H.
  + by move=> {fn f H} [fn f] [fn' f'] /=; t_xrbindP.
  exists f' => //.
  by move: hF; t_xrbindP => f'' /add_finfoP /add_funnameP -> ->.
Qed.

Lemma get_map_cfprog_gen {T1 T2} (info : T1 -> fun_info) (F: T1 -> cexec T2) p p' fn f:
  map_cfprog_gen info F p = ok p' ->
  get_fundef p fn = Some f ->
  exists2 f', F f = ok f' & get_fundef p' fn = Some f'.
Proof. by apply get_map_cfprog_name_gen. Qed.

Lemma get_map_cfprog_name_gen' {T1 T2} (info : T1 -> fun_info) (F: funname -> T1 -> cexec T2) p p' fn f':
  map_cfprog_name_gen info F p = ok p' ->
  get_fundef p' fn = Some f' ->
  exists2 f, F fn f = ok f' & get_fundef p fn = Some f.
Proof.
  move=> Hmap H.
  have [|f /= hF hf] := mapM_assoc' _ Hmap H.
  + by move=> {fn f' H} [fn f] [fn' f'] /=; t_xrbindP.
  exists f => //.
  by move: hF; t_xrbindP=> f'' /add_finfoP /add_funnameP -> ->.
Qed.

Lemma get_map_cfprog_gen' {T1 T2} (info: T1 -> fun_info) (F: T1 -> cexec T2) p p' fn f':
  map_cfprog_gen info F p = ok p' ->
  get_fundef p' fn = Some f' ->
  exists2 f, F f = ok f' & get_fundef p fn = Some f.
Proof. by apply get_map_cfprog_name_gen'. Qed.

(* -------------------------------------------------------- *)
(* Internal error                                           *)

Definition pp_internal_error (pass:string) (pp : pp_error) := {|
  pel_msg := pp;
  pel_fn := None;
  pel_fi := None;
  pel_ii := None;
  pel_vi := None;
  pel_pass := Some pass;
  pel_internal := true
|}.

Definition pp_internal_error_s (pass:string) (s:string) :=
  pp_internal_error pass (pp_s s).

Definition pp_internal_error_s_at pass (ii:instr_info) (s:string) :=
  pp_at_ii ii (pp_internal_error_s pass s).


Module Type LoopCounter.
  Parameter nb  : nat.
  Parameter nbP : nb = (nb.-1).+1.
End LoopCounter.

Module Loop : LoopCounter.
  Definition nb := 100.
  Lemma nbP : nb = (nb.-1).+1.
  Proof. done. Qed.
End Loop.

Ltac t_xrbindP :=
  match goal with
  | [ |- Result.bind _ _ = Ok _ _ -> _ ] =>
      apply: rbindP; t_xrbindP

  | [ |- Result.map _ _ = Ok _ _ -> _ ] =>
      rewrite /rmap; t_xrbindP

  | [ |- assert _ _ = Ok _ _ -> _ ] =>
      move=> /assertP; t_xrbindP

  | [ |- unit -> _ ] =>
      case; t_xrbindP

  | [ |- add_finfo _ _ = ok _ -> _] => 
      move=> /add_finfoP; t_xrbindP

  | [ |- add_funname _ _ = ok _ -> _] => 
      move=> /add_funnameP; t_xrbindP

  | [ |- add_iinfo _ _ = ok _ -> _] => 
      move=> /add_iinfoP; t_xrbindP

  | [ |- ok _ = ok _ -> _ ] =>
      case; t_xrbindP

  | [ |- forall h, _ ] =>
      let hh := fresh h in move=> hh; t_xrbindP; move: hh

  | _ => idtac
  end.

(* Predefined errors *)

Definition gen_loop_iterator pass_name (ii:option instr_info) :=
  {| pel_msg      := pp_s "loop iterator too small"
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := true
  |}.

Definition loop_iterator pass_name := 
  gen_loop_iterator pass_name None.

Definition ii_loop_iterator pass_name ii := 
  gen_loop_iterator pass_name (Some ii).

Definition error_copy_remain := "array copy remain"%string.
