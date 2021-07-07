Require Import ZArith Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr.

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

(*
Variant box := 
  | Vbox
  | Hbox
  | HoVbox.

Inductive pp_error :=
  | PPEstring  `(string)
  | PPEvar     `(var)
  | PPEop1     `(sop1)
  | PPEop2     `(sop2)
  | PPEopN     `(opN)
  | PPEsopn    `(sopn)
  | PPEexpr    `(pexpr)
  | PPElval    `(lval)
  | PPEfunname `(funname)
  | PPEinstr   `(instr_r)
  | PPEiinfo   `(instr_info)
  | PPEbox     `(box) `(seq pp_error)
  | PPEbreack.

(*
Fixpoint pp_seq_aux sep (xs: list pp_error) := 
  match xs with
  | [::] => [::]
  | x::xs => sep :: x:: pp_seq_aux sep xs
  end.

Definition pp_seq_sep sep xs := 
  PPEseq match xs with
  | [::] => [::]
  | [::x] => [::x]
  | x::xs => x:: pp_seq_aux sep xs
  end.

Definition pp_seq := pp_seq_sep PPEbreack.

Definition pp_list_sep {A:Type} sep (pp_e: A -> pp_error) xs :=
  pp_seq_sep sep (map pp_e xs).

Definition pp_list A := @pp_list_sep A PPEbreack.
*)

Definition pp_hov  := PPEbox HoVbox.
Definition pp_box := PPEbox Hbox.
Definition pp_vbox := PPEbox Vbox.

Definition pp_s    := PPEstring.
Definition pp_v    := PPEvar.
Definition pp_op1  := PPEop1.

Definition pp_neq {A:Type} (pp_e: A -> pp_error) e1 e2 (_: unit):=
  pp_hov [:: pp_e e1; pp_s "should be equal to"; pp_e e2].

Definition pp_at (ii:instr_info) (e:pp_error) := 
  pp_box [:: pp_s "at "; PPEiinfo ii].
*)

Variant asm_error :=
  | AsmErr_string of string & option pexpr
  | AsmErr_cond of pexpr.

Inductive error_msg :=
  | Cerr_varalloc : var_i -> var_i -> string -> error_msg
  | Cerr_inline   : Sv.t -> Sv.t -> error_msg
  | Cerr_Loop     : string -> error_msg
  | Cerr_fold2    : string -> error_msg
  | Cerr_neqty    : stype -> stype -> string -> error_msg
  | Cerr_neqop1   : sop1 -> sop1 -> string -> error_msg
  | Cerr_neqop2   : sop2 -> sop2 -> string -> error_msg
  | Cerr_neqopN   : opN -> opN -> string -> error_msg
  | Cerr_neqop    : sopn -> sopn -> string -> error_msg
  | Cerr_neqdir   : string -> error_msg
  | Cerr_neqexpr  : pexpr -> pexpr -> string -> error_msg
  | Cerr_neqlval  : lval -> lval -> string -> error_msg
  | Cerr_neqfun   : funname -> funname -> string -> error_msg
  | Cerr_neqinstr : instr_r -> instr_r -> string -> error_msg
  | Cerr_unknown_fun : funname -> string -> error_msg
  | Cerr_in_fun   : fun_error -> error_msg
  | Cerr_arr_exp  : pexpr -> pexpr -> error_msg
  | Cerr_arr_exp_v: lval -> lval -> error_msg
  | Cerr_stk_alloc: string -> error_msg
  | Cerr_one_varmap: string -> error_msg
  | Cerr_one_varmap_free: funname -> seq var -> error_msg
  | Cerr_linear   : string -> error_msg
  | Cerr_tunneling : string -> error_msg
  | Cerr_needspill  : funname -> seq var -> error_msg
  | Cerr_assembler: asm_error -> error_msg

with fun_error   :=
  | Ferr_in_body  : funname -> funname -> (instr_info * error_msg) -> fun_error
  | Ferr_neqfun   : funname -> funname -> fun_error
  | Ferr_fun      : funname -> error_msg -> fun_error
  | Ferr_remove_glob     : instr_info -> var_i -> fun_error
  | Ferr_remove_glob_dup : instr_info -> var -> fun_error
  | Ferr_msg      : error_msg -> fun_error
  | Ferr_neqprog  : fun_error
  | Ferr_loop     : fun_error
  | Ferr_uniqfun  : fun_error
  | Ferr_uniqglob : fun_error
  | Ferr_topo     : fun_error
  | Ferr_lowering : fun_error
  | Ferr_glob_neq : fun_error.


Notation instr_error := (instr_info * error_msg)%type.

Definition cexec A := result error_msg A.
Definition ciexec A := result instr_error A.
Definition cfexec A := result fun_error A.

Definition cok {A} (a:A) : cexec A := @Ok error_msg A a.
Definition ciok {A} (a:A) : ciexec A := @Ok instr_error A a.
Definition cfok {A} (a:A) : cfexec A := @Ok fun_error A a.

Definition cerror  (c:error_msg) {A} : cexec A := @Error _ A c.
Definition cierror (ii:instr_info) (c:error_msg) {A} : ciexec A := @Error _ A (ii,c).
Definition cferror  (c:fun_error) {A} : cfexec A := @Error _ A c.

Definition add_iinfo {A} ii (r:cexec A) : ciexec A :=
  match r with
  | Ok a => @Ok _ A a
  | Error e  => Error (ii,e)
  end.

Definition add_finfo {A} f1 f2 (r:ciexec A) : cfexec A :=
  match r with
  | Ok a => @Ok _ A a
  | Error e  => Error (Ferr_in_body f1 f2 e)
  end.

Definition add_infun {A} (ii:instr_info) (r:cfexec A) : ciexec A :=
  match r with
  | Ok a => @Ok _ A a
  | Error e => Error (ii, Cerr_in_fun e)
  end.

Definition add_err_msg (A : Type) (r : cexec A) := 
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_msg e)
  end.

Definition add_err_fun (A : Type) (f : funname) (r : cexec A) :=
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

Lemma add_iinfoP A (a:A) (e:cexec A) ii (P:Prop):
  (e = ok a -> P) ->
  add_iinfo ii e = ok a -> P.
Proof. by case: e=> //= a' H [] Heq;apply H;rewrite Heq. Qed.

Lemma add_finfoP A (a:A) e f1 f2 (P:Prop):
  (e = ok a -> P) ->
  add_finfo f1 f2 e = ok a -> P.
Proof. by case: e=> //= a' H [] Heq;apply H;rewrite Heq. Qed.

Lemma add_infunP A a ii (e:cfexec A) (P:Prop):
  (e = ok a -> P) ->
  add_infun ii e = ok a -> P.
Proof. by case: e=> //= a' H [] Heq;apply H;rewrite Heq. Qed.

Lemma add_err_msgP A (a: A) e (P:Prop):
  (e = ok a -> P) ->
  add_err_msg e = ok a -> P.
Proof. by case: e => //= ? h [] heq; apply: h;rewrite heq. Qed.

Definition map_cfprog_name {T1 T2} (F: funname -> T1 -> ciexec T2) :=
  mapM (fun (f:funname * T1) => Let x := add_finfo f.1 f.1 (F f.1 f.2) in cfok (f.1, x)).

Definition map_cfprog {T1 T2} (F: T1 -> ciexec T2) :=
  map_cfprog_name (fun _ t1 => F t1).

Lemma get_map_cfprog_name {T1 T2} (F: funname -> T1 -> ciexec T2) p p' fn f:
  map_cfprog_name F p = ok p' ->
  get_fundef p fn = Some f ->
  exists2 f', F fn f = ok f' & get_fundef p' fn = Some f'.
Proof.
  move=> Hmap H.
  have [|f' /= hF hf'] := mapM_assoc _ Hmap H.
  + move=> {fn f H} [fn f] [fn' f'] /=.
    t_xrbindP=> f''.
    by apply: add_finfoP => _ [<- _].
  exists f' => //.
  move: hF; t_xrbindP=> f''.
  by apply: add_finfoP => ? [<-].
Qed.

Lemma get_map_cfprog {T1 T2} (F: T1 -> ciexec T2) p p' fn f:
  map_cfprog F p = ok p' ->
  get_fundef p fn = Some f ->
  exists2 f', F f = ok f' & get_fundef p' fn = Some f'.
Proof. apply get_map_cfprog_name. Qed.

Lemma get_map_cfprog_name' {T1 T2} (F: funname -> T1 -> ciexec T2) p p' fn f':
  map_cfprog_name F p = ok p' ->
  get_fundef p' fn = Some f' ->
  exists2 f, F fn f = ok f' & get_fundef p fn = Some f.
Proof.
  move=> Hmap H.
  have [|f /= hF hf] := mapM_assoc' _ Hmap H.
  + move=> {fn f' H} [fn f] [fn' f'] /=.
    t_xrbindP=> f''.
    by apply: add_finfoP => _ [<- _].
  exists f => //.
  move: hF; t_xrbindP=> f''.
  by apply: add_finfoP => ? [<-].
Qed.

Lemma get_map_cfprog' {T1 T2} (F: T1 -> ciexec T2) p p' fn f':
  map_cfprog F p = ok p' ->
  get_fundef p' fn = Some f' ->
  exists2 f, F f = ok f' & get_fundef p fn = Some f.
Proof. apply get_map_cfprog_name'. Qed.

Module Type LoopCounter.
  Parameter nb  : nat.
  Parameter nbP : nb = (nb.-1).+1.
End LoopCounter.

Module Loop : LoopCounter.
  Definition nb := 100.
  Lemma nbP : nb = (nb.-1).+1.
  Proof. done. Qed.
End Loop.
