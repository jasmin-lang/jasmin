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

(* TODO: Merge map_cfprog and map_cfprog_leak *)
Definition map_cfprog_leak {T1 T2 T3} (F: T1 -> ciexec (T2 * T3)) lt1:
  cfexec (seq (funname * T2) * seq (funname * T3)) :=
  Let l := mapM (fun (f:funname * T1) => Let x := add_finfo f.1 f.1 (F f.2) in cfok (f.1, x)) lt1 in
  let l1 := map (fun p => (p.1, p.2.1)) l in
  let l2 := map (fun p => (p.1, p.2.2)) l in
  ok (l1, l2).


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

Lemma map_cfprog_get_fd {T1 T2 T3} (F: T1 -> ciexec (T2 * T3)) p p' lt fn (f: T1) (f': T2):
  map_cfprog_leak F p = ok p' ->
  get_fundef p fn = Some f ->
  F f = ok (f', lt) ->
  get_fundef p'.1 fn = Some f'.
Proof.
  elim: p p'=> // -[fn1 fd1] pl IH p'.
  rewrite /map_cfprog_leak /= -/(map_cfprog_leak _ _).
  apply: rbindP. move=> fdlts.
  apply: rbindP. move=> fdlts'.
  apply: rbindP. move=> [fd' lt'] Hpl' [] <- /=. t_xrbindP.
  move=> fdlts'' Hm <- <-.
  case: ifP.
  + move=> /eqP Hfn.
    move=> [] <- Hf.
    rewrite Hf in Hpl'.
    move: Hpl'. move=> -[] <- <- /=.
    rewrite Hfn. case: eqP.
    by move=> h.
    move=>h. by case h.
  + move=> Hfn Hf Hf' /=. rewrite Hfn /=.
    rewrite /map_cfprog_leak in IH.
    rewrite Hm in IH. rewrite /= in IH.
    move: (IH (([seq (p.1, p.2.1) | p <- fdlts''], [seq (p.1, p.2.2) | p <- fdlts'']))).
    rewrite /=. move=> H. apply H; auto.
Qed.

Lemma map_cfprog_get_leak {T1 T2 T3} (F: T1 -> ciexec (T2 * T3)) p p' lt fn (f: T1) (f': T2):
  map_cfprog_leak F p = ok p' ->
  get_fundef p fn = Some f ->
  F f = ok (f', lt) ->
  get_leak p'.2 fn = Some lt.
Proof.
  elim: p p'=> // -[fn1 fd1] pl IH p'.
  rewrite /map_cfprog_leak /= -/(map_cfprog_leak _ _).
  apply: rbindP. move=> fdlts.
  apply: rbindP. move=> fdlts'.
  apply: rbindP. move=> [fd' lt'] Hpl' [] <- /=. t_xrbindP.
  move=> fdlts'' Hm <- <-.
  case: ifP.
  + move=> /eqP Hfn.
    move=> [] <- Hf.
    rewrite Hf in Hpl'.
    move: Hpl'. move=> -[] <- <- /=.
    rewrite Hfn. case: eqP.
    by move=> h.
    move=>h. by case h.
  + move=> Hfn Hf Hf' /=. rewrite Hfn /=.
    rewrite /map_cfprog_leak in IH.
    rewrite Hm in IH. rewrite /= in IH.
    move: (IH (([seq (p.1, p.2.1) | p <- fdlts''], [seq (p.1, p.2.2) | p <- fdlts'']))).
    rewrite /=. move=> H. apply H; auto.
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

Lemma get_map_cfprog_leak {T1 T2 T3} (F: T1 -> ciexec (T2*T3))
      p p' fn f:
  map_cfprog_leak F p = ok p' ->
  get_fundef p fn = Some f ->
  exists f', exists lt,
   [/\ F f = ok (f', lt), 
       get_fundef (p'.1) fn = Some f' &
       get_leak (p'.2) fn = Some lt].
Proof.
  move=> Hmap H.
  have Hp := (get_fundef_in' H).
  have Hu := Hmap.
  rewrite /map_cfprog_leak in Hmap. move: Hmap.
  t_xrbindP. move=> flts Hmap <- /=.
  move: (mapM_In Hmap Hp). move=> [] [fn' [fd' lt']] [] /= Hfd Hok.
  apply: rbindP Hok. move=> [f' lt''] Hafn [] Hfn' Hfd' Hlt' /=.
  have Hf: F f = ok (f', lt'').
  rewrite /add_finfo in Hafn.
  by case: (F f) Hafn=> // a []<-.
  exists f'; exists lt''.
  move: (map_cfprog_get_fd Hu H Hf).
  move: (map_cfprog_get_leak Hu H Hf).
  move=> H1 H2.
  rewrite /map_cfprog_leak in Hu. rewrite Hmap in Hu.
  move: Hu. t_xrbindP. move=> ys <- hp. rewrite -hp in H2.
  rewrite /= in H2; auto. rewrite -hp in H1.
  rewrite /= in H1. split; auto.
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

Definition map_prog_leak {T1 T2 T3} (F: T1 -> (T2 * T3)) l:
  (seq (funname * T2) * seq (funname * T3)) :=
  let l := map (fun t => (t.1, F t.2)) l in
  (map (fun t : funname * (T2 * T3) => (t.1, t.2.1)) l,
   map (fun t : funname * (T2 * T3) => (t.1, t.2.2)) l).

Lemma map_prog_get_fd {T1 T2 T3} (F: T1 -> (T2 * T3)) p p' lt fn (f: T1) (f': T2):
  map_prog_leak F p = p' ->
  get_fundef p fn = Some f ->
  F f = (f', lt) ->
  get_fundef p'.1 fn = Some f'.
Proof.
  elim: p p'=> // -[fn1 fd1] pl IH p'.
  rewrite /map_prog_leak /= -/(map_prog_leak _ _). case:p'.
  move=> fs ls H.
  case: ifP.
  + move=> /eqP Hfn.
    move=> [] <- Hf.
    rewrite Hf in H.
    case: H => H1 H2.
    rewrite -H1. rewrite /=.
    case: eqP.
    move=> H'. auto.
    move=> h. by case h.
  move=> Hfn Hf Hf' /=. case: H=> H1 H2.
  rewrite -H1 /=. rewrite Hfn /=.
  rewrite /map_prog_leak /= in IH.
  move: (IH  ([seq (t.1, t.2.1) | t <- [seq (t.1, F t.2) | t <- pl]], [seq (t.1, t.2.2) | t <- [seq (t.1, F t.2) | t <- pl]])).
  rewrite /=. move=> H. apply H; eauto.
Qed.

Lemma map_prog_get_leak {T1 T2 T3} (F: T1 -> (T2 * T3)) p p' lt fn (f: T1) (f': T2):
  map_prog_leak F p = p' ->
  get_fundef p fn = Some f ->
  F f = (f', lt) ->
  get_leak p'.2 fn = Some lt.
Proof.
  elim: p p'=> // -[fn1 fd1] pl IH p'.
  rewrite /map_prog_leak /= -/(map_prog_leak _ _). case:p'.
  move=> fs ls H.
  case: ifP.
  + move=> /eqP Hfn.
    move=> [] <- Hf.
    rewrite Hf in H.
    case: H => H1 H2.
    rewrite -H2. rewrite /=.
    case: eqP.
    move=> H'. auto.
    move=> h. by case h.
  move=> Hfn Hf Hf' /=. case: H=> H1 H2.
  rewrite -H2 /=. rewrite Hfn /=.
  rewrite /map_prog_leak /= in IH.
  move: (IH  ([seq (t.1, t.2.1) | t <- [seq (t.1, F t.2) | t <- pl]], [seq (t.1, t.2.2) | t <- [seq (t.1, F t.2) | t <- pl]])).
  rewrite /=. move=> H. apply H; eauto.
Qed.


Lemma get_map_prog_leak {T} (F: fundef -> (fundef*T))
      p p' fn f:
  map_prog_leak F p = p' ->
  get_fundef p fn = Some f ->
  exists f', exists lt,
   [/\ F f = (f', lt), 
       get_fundef p'.1 fn = Some f' &
       get_leak p'.2 fn = Some lt].
Proof.
  case p'. move=> fs ls.
  move=> Hmap H.
  have Hp := (get_fundef_in' H).
  have Hu := Hmap.
  rewrite /map_prog_leak in Hmap.
  have Hf: F f = ((F f).1, (F f).2).
  by case (F f).
  exists (F f).1. exists (F f).2.
  move: (map_prog_get_fd Hu H Hf).
  move: (map_prog_get_leak Hu H Hf).
  split=> //.
Qed.

Definition map_fnprog_leak {T1 T2 T3} (F: (funname * T1) -> cfexec (T2 * T3)) lt1 :
  cfexec (seq (funname * T2) * seq (funname * T3)) :=
  Let l := mapM (fun (f:funname * T1) => 
      Let r := (F (f.1, f.2)) in ok (f.1, r)) lt1 in
  ok (map (fun t : funname * (T2 * T3) => (t.1, t.2.1)) l,
      map (fun t : funname * (T2 * T3) => (t.1, t.2.2)) l).


(*Definition map_fnprog_leak {T1 T2 T3} (F: funname -> T1 -> ciexec (T2 * T3)) lt1 :
  cfexec (seq (funname * T2) * seq (funname * T3)) :=
  Let l := mapM (fun (f:funname * T1) => 
      Let r := add_finfo f.1 f.1 (F f.1 f.2) in ok (f.1, r)) lt1 in
  ok (map (fun t : funname * (T2 * T3) => (t.1, t.2.1)) l,
      map (fun t : funname * (T2 * T3) => (t.1, t.2.2)) l).*)

(*Definition map_cfprog_leak' {T1 T2 T3} (F: T1 -> ciexec (T2 * T3)) := 
  map_fnprog_leak (fun (fn:funname) fd => F fd).

Definition map_prog_leak' {T1 T2 T3} (F: T1 -> (T2 * T3)) := 
   map_cfprog_leak' (fun t1 => ok (F t1)).*)


Lemma map_fnprog_get_fd {T2 T3} (F: (funname * T2) -> cfexec (T2 * T3)) p p' lt fn f fd':
  map_fnprog_leak F p = ok p' ->
  get_fundef p fn = Some f ->
  F (fn, f) = ok (fd', lt) ->
  get_fundef p'.1 fn = Some fd'.
Proof.
  elim: p p'=> // -[fn1 fd1] pl IH p'.
  rewrite /map_fnprog_leak /= -/(map_fnprog_leak _ _).
  apply: rbindP. move=> fdlts.
  apply: rbindP. move=> fdlts'.
  apply: rbindP. move=> [fd'' lt'] Hpl' [] <- /=. t_xrbindP.
  move=> fdlts'' Hm <- <-.
  case: ifP.
  + move=> /eqP Hfn.
    move=> [] <- Hf.
    rewrite Hfn in Hf.
    rewrite Hf in Hpl'.
    move: Hpl'. move=> -[] <- <- /=.
    rewrite Hfn. case: eqP.
    by move=> h.
    move=>h. by case h.
  + move=> Hfn Hf Hf' /=.
    rewrite /map_fnprog_leak in IH.
    rewrite Hm in IH. rewrite /= in IH.
    move: (IH ([seq (t.1, t.2.1) | t <- fdlts''], [seq (t.1, t.2.2) | t <- fdlts''])). rewrite Hfn /=.
    rewrite /=. move=> H.
    apply H; auto.
Qed.

Lemma map_fnprog_get_leak {T2 T3} (F: (funname * T2) -> cfexec (T2 * T3)) p p' lt fn f fd':
  map_fnprog_leak F p = ok p' ->
  get_fundef p fn = Some f ->
  F (fn, f) = ok (fd', lt) ->
  get_leak p'.2 fn = Some lt.
Proof.
  elim: p p'=> // -[fn1 fd1] pl IH p'.
  rewrite /map_fnprog_leak /= -/(map_fnprog_leak _ _).
  apply: rbindP. move=> fdlts.
  apply: rbindP. move=> fdlts'.
  apply: rbindP. move=> [fd'' lt'] Hpl' [] <- /=. t_xrbindP.
  move=> fdlts'' Hm <- <-.
  case: ifP.
  + move=> /eqP Hfn.
    move=> [] <- Hf.
    rewrite Hfn in Hf.
    rewrite Hf in Hpl'.
    move: Hpl'. move=> -[] <- <- /=.
    rewrite Hfn. case: eqP.
    by move=> h.
    move=>h. by case h.
  + move=> Hfn Hf Hf' /=. rewrite Hfn /=.
    rewrite /map_fnprog_leak in IH.
    rewrite Hm in IH. rewrite /= in IH.
    move: (IH  ([seq (t.1, t.2.1) | t <- fdlts''], [seq (t.1, t.2.2) | t <- fdlts''])).
    rewrite /=. move=> H. apply H; auto.
Qed.

Lemma get_map_fnprog_leak {T2 T3} (F: (funname * T2) -> cfexec (T2 * T3))
      p p' fn f:
  map_fnprog_leak F p = ok p' ->
  get_fundef p fn = Some f ->
  exists fd', exists lt,
   [/\ F (fn, f) = ok (fd', lt),
       get_fundef (p'.1) fn = Some fd' &
       get_leak (p'.2) fn = Some lt].
Proof.
  move=> Hmap H.
  have Hp := (get_fundef_in' H).
  have Hu := Hmap.
  rewrite /map_fnprog_leak in Hmap. move: Hmap.
  t_xrbindP. move=> flts Hmap <- /=.
  move: (mapM_In Hmap Hp).
  move=> [] [fn'' [fd' lt]] /= [] Hfd Hok.
  apply: rbindP Hok. move=> [f' lt''] Hafn [] Hfn' Hfd' Hlt' /=.
  have Hf: F (fn, f) = ok (fd', lt'').
  rewrite /add_finfo in Hafn.
  case: (F (fn, f)) Hafn => // a [] ->. by rewrite Hfd'.
  exists fd'; exists lt''.
  move: (map_fnprog_get_fd Hu H Hf).
  move: (map_fnprog_get_leak Hu H Hf).
  move=> H1 H2.
  rewrite /map_fnprog_leak in Hu. rewrite Hmap in Hu.
  move: Hu. t_xrbindP. move=> ys <- hp. rewrite -hp in H2.
  rewrite /= in H2; auto. rewrite -hp in H1.
  rewrite /= in H1. split; auto.
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
