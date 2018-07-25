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

Variant asm_error :=
  | AsmErr_string : string -> asm_error
  | AsmErr_cond   : pexpr -> asm_error.

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
  | Cerr_linear   : string -> error_msg
  | Cerr_assembler: asm_error -> error_msg
 
with fun_error   := 
  | Ferr_in_body  : funname -> funname -> (instr_info * error_msg) -> fun_error
  | Ferr_neqfun   : funname -> funname -> fun_error
  | Ferr_fun      : funname -> error_msg -> fun_error
  | Ferr_remove_glob     : instr_info -> var_i -> fun_error
  | Ferr_remove_glob_dup : instr_info -> global -> fun_error
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

Definition map_cfprog {T1 T2} (F: T1 -> ciexec T2) :=
  mapM (fun (f:funname * T1) => Let x := add_finfo f.1 f.1 (F f.2) in cfok (f.1, x)).

(* Note: this lemma cannot be extended to mapM because it needs the names to be conserved *)
Lemma map_cfprog_get {T1 T2} F p p' fn (f: T1) (f': T2):
  map_cfprog F p = ok p' ->
  get_fundef p fn = Some f ->
  F f = ok f' ->
  get_fundef p' fn = Some f'.
Proof.
  elim: p p'=> // -[fn1 fd1] pl IH p'.
  rewrite /map_cfprog /= -/(map_cfprog _ _).
  apply: rbindP=> -[fn1' fd1']; apply: rbindP=> fd1'' Hfd1 [] Hfn1 Hfd1''.
  subst fn1'; subst fd1''.
  apply: rbindP=> pl' Hpl' [] <-.
  rewrite get_fundef_cons /=.
  case: ifP.
  + move=> /eqP Hfn.
    subst fn1=> -[] Hf.
    subst fd1=> Hf'.
    rewrite Hf' in Hfd1.
    by move: Hfd1=> -[] ->.
  + move=> Hfn Hf Hf'.
    exact: IH.
Qed.

Lemma get_map_cfprog {T1 T2} (F: T1 -> ciexec T2) p p' fn f:
  map_cfprog F p = ok p' ->
  get_fundef p fn = Some f ->
  exists f', F f = ok f' /\ get_fundef p' fn = Some f'.
Proof.
  move=> Hmap H.
  have Hp := (get_fundef_in' H).
  move: (mapM_In Hmap Hp)=> [[fn' fd'] /= [Hfd Hok]].
  apply: rbindP Hok=> f' Hf' [] Hfn' Hfd'.
  subst fn'; subst fd'.
  have Hf: F f = ok f'.
    rewrite /add_finfo in Hf'.
    by case: (F f) Hf'=> // a []<-.
  exists f'; split=> //.
  exact: (map_cfprog_get Hmap H).
Qed.

Lemma get_map_cfprog' {T1 T2} (F: T1 -> ciexec T2) p p' fn f':
  map_cfprog F p = ok p' ->
  get_fundef p' fn = Some f' ->
  exists2 f, F f = ok f' & get_fundef p fn = Some f.
Proof.
  elim: p p' f'.
  + by move => _ f' [<-].
  case => n d p ih p'' f' /=; t_xrbindP => - [x y] d'; apply: add_finfoP => ok_d' [??]; subst x y => p' rec <- {p''} /=.
  case: ifP.
  + by move => _ [<-]; eauto.
  by move => _ /(ih _ _ rec).
Qed.

Module Type LoopCounter.
  Parameter nb  : nat.
  Parameter nbP : nb = (nb.-1).+1.
End LoopCounter.

Module Loop : LoopCounter.
  Definition nb := 100.
  Lemma nbP : nb = (nb.-1).+1.
  Proof. done. Qed.
End Loop.
