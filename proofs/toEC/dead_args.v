From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import expr compiler_util dead_code.

Local Open Scope seq_scope.

(* ** Dead code, dead parameters and dead results

   The pass removes the code that computes nothing used, as [dead_code] does,
   and, across the functions, the parameters whose value nothing uses and the
   results that no caller uses, with the matching arguments and destinations
   at the call sites.

   Which parameters and results are dead is computed by an oracle,
   [dead_info], over the whole program at once: a parameter may be used only
   to compute a result, and this result only to compute the argument given
   to this parameter at another call (a mask passed around a loop), so that
   a removal one at a time would remove neither. A round of the pass:
   - removes the parameters that the oracle tells dead, and the corresponding
     arguments at the call sites; a removed parameter becomes a local
     variable;
   - runs [dead_code] with the results that the oracle tells dead: it
     removes them, and the corresponding destinations, which it checks to be
     dead ([check_keep_only]), and the code that computes nothing used;
   - checks that no removed parameter is live at the entry of the body: its
     value is not used.
   The rounds are repeated until one removes no parameter and no result: a
   removal can make other code dead. Each round that does not stop removes at
   least one parameter or result, so that their number bounds the number of
   rounds.

   The parameters and results for which [protect] holds are kept: the
   signature of a function called from outside the program, from EasyCrypt,
   is fixed by the caller of the pass.

   The calls are kept, even when their results are all dead: the callee may
   fail, write the memory or make a system call. *)

Module Import E.

  Definition pass : string := "dead arguments".

  Definition live_param_error :=
    pp_internal_error_s pass "a parameter told dead is live".

End E.

Section ASM_OP.

Context `{asmop : asmOp} {LC : LoopCounter}.

(* The parameters and results of a function that are kept. *)
Context (protect : funname -> var -> bool).

(* For each function, the parameters and the results that are kept: [Some k]
   where [k] tells, for each of them, whether it is used, or [None] when they
   all are. Computed in OCaml. *)
Context (dead_info : _uprog -> funname -> option (seq bool) * option (seq bool)).

Notation dead_code_i := (dead_code_i (fun _ => false) false).

(* The positions kept by [keep_only l k], then by [keep_only _ k']: those
   kept by [keep_compose k k'] in [l]. *)
Fixpoint keep_compose (k k' : seq bool) : seq bool :=
  match k with
  | [::] => [::]
  | false :: k => false :: keep_compose k k'
  | true :: k =>
    match k' with
    | [::] => true :: keep_compose k [::]
    | b :: k' => b :: keep_compose k k'
    end
  end.

(* The variables of [xs] kept: those that [o] tells used, and the protected
   ones. *)
Definition keep_vars (fn : funname) (o : option (seq bool)) (xs : seq var_i) :=
  if o is Some k then
    let k := [seq b.1 || protect fn (v_var b.2) | b <- zip k xs] in
    if all id k then None else Some k
  else None.

Definition params_keep (info : funname -> option (seq bool) * option (seq bool)) (p : _uprog) (fn : funname) : option (seq bool) :=
  if get_fundef (p_funcs p) fn is Some fd then keep_vars fn (info fn).1 fd.(f_params)
  else None.

Definition res_keep (info : funname -> option (seq bool) * option (seq bool)) (p : _uprog) (fn : funname) : option (seq bool) :=
  if get_fundef (p_funcs p) fn is Some fd then keep_vars fn (info fn).2 fd.(f_res)
  else None.

Section ARGS.

Context (kp : funname -> option (seq bool)).

Fixpoint rm_args_i (i : instr) : instr :=
  let 'MkI ii ir := i in
  let ir :=
    match ir with
    | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ | Cassert _ => ir
    | Ccall xs fn es => Ccall xs fn (fn_keep_only kp fn es)
    | Cif e c1 c2 => Cif e (map rm_args_i c1) (map rm_args_i c2)
    | Cfor x r c => Cfor x r (map rm_args_i c)
    | Cwhile a c1 e ii_w c2 => Cwhile a (map rm_args_i c1) e ii_w (map rm_args_i c2)
    end in
  MkI ii ir.

Definition rm_params_fd (fn : funname) (fd : ufundef) : ufundef :=
  {| f_info := fd.(f_info);
     f_contract := fd.(f_contract);
     f_tyin := fn_keep_only kp fn fd.(f_tyin);
     f_params := fn_keep_only kp fn fd.(f_params);
     f_body := map rm_args_i fd.(f_body);
     f_tyout := fd.(f_tyout);
     f_res := fd.(f_res);
     f_extra := fd.(f_extra);
  |}.

(* The parameters of [fd] that [kp] removes are not live at the entry of its
   body once these parameters are removed, as [dead_code] computes the
   liveness when it removes the results that [kr] tells dead. *)
Definition check_params (kr : funname -> option (seq bool)) (fn : funname) (fd : ufundef) :
  cexec unit :=
  if kp fn is Some k then
    let fd' := rm_params_fd fn fd in
    let s := read_es (map Plvar (fn_keep_only kr fn fd'.(f_res))) in
    Let sc := dead_code_c (dead_code_i kr) fd'.(f_body) s in
    assert (all (fun b => b.1 || ~~ Sv.mem (v_var b.2) sc.1) (zip k fd.(f_params)))
      live_param_error
  else ok tt.

End ARGS.

(* For each function of the source, the parameters and the results that are
   kept in the result of the pass. *)
Definition keep_info := seq (funname * (seq bool * seq bool)).

Definition keep_update (k : seq bool) (o : option (seq bool)) : seq bool :=
  if o is Some k' then keep_compose k k' else k.

Definition update_info kp kr (info : keep_info) : keep_info :=
  [seq (f.1, (keep_update f.2.1 (kp f.1), keep_update f.2.2 (kr f.1))) | f <- info].

(* A round: the program, whether it removed a parameter or a result, and the
   parameters and the results it kept. *)
Definition dead_args_round (p : _uprog) :
  cexec (_uprog * bool * (funname -> option (seq bool)) * (funname -> option (seq bool))) :=
  let info := dead_info p in
  let kp := params_keep info p in
  let kr := res_keep info p in
  let p1 := map_prog_name (pT := progUnit) (rm_params_fd kp) p in
  Let p2 := dead_code_prog_tokeep (pT := progUnit) (fun _ => false) (fun _ fi => fi) false kr p1 in
  Let _ := allM (fun f => add_funname f.1 (check_params kp kr f.1 f.2)) (p_funcs p) in
  let changed := has (fun f => isSome (kp f.1) || isSome (kr f.1)) (p_funcs p) in
  ok (p2, changed, kp, kr).

Fixpoint dead_args_loop (fuel : nat) (p : _uprog) (info : keep_info) : cexec (_uprog * keep_info) :=
  match fuel with
  | O => ok (p, info)
  | S fuel =>
    Let r := dead_args_round p in
    let '(p, changed, kp, kr) := r in
    let info := update_info kp kr info in
    if changed then dead_args_loop fuel p info else ok (p, info)
  end.

Definition dead_args_info (p : _uprog) : cexec (_uprog * keep_info) :=
  let info := [seq (f.1, (nseq (size f.2.(f_params)) true, nseq (size f.2.(f_res)) true))
              | f <- p_funcs p] in
  let fuel := (sumn [seq size f.2.(f_params) + size f.2.(f_res) | f <- p_funcs p]).+1 in
  dead_args_loop fuel p info.

Definition dead_args_prog (p : _uprog) : cexec _uprog :=
  Let r := dead_args_info p in ok r.1.

End ASM_OP.
