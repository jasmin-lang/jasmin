From mathcomp Require Import all_ssreflect all_algebra.
Require Import
  oseq
  compiler_util
  expr
  one_varmap
  linear
  low_memory
  lea.
Require Import
  arch_decl
  arch_extra.
Import Utf8 String.
Import all_ssreflect.
Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module E.

Definition pass_name := "asmgen"%string.

Definition gen_error (internal:bool) (ii:option instr_info) (vi: option var_info) (msg:pp_error) := 
  {| pel_msg      := msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := vi
   ; pel_pass     := Some pass_name
   ; pel_internal := internal
  |}.

Definition internal_error ii msg := 
  gen_error true (Some ii) None (pp_s msg).

Definition error ii msg := 
  gen_error false (Some ii) None msg.

Definition verror internal msg ii (v:var_i) := 
  gen_error internal (Some ii) (Some v.(v_info)) (pp_box [:: pp_s msg; pp_s ":"; pp_var v]).

Definition invalid_name category ii (v:var_i) :=
   verror true ("Invalid " ++ category ++ " name") ii v.

Definition invalid_ty category ii (v:var_i) :=
  verror true ("Invalid " ++ category ++ " type") ii v.

Definition invalid_flag ii (v:var_i) :=
   verror false ("Invalid name for rflag (check initialization?)") ii v.

Definition berror ii e msg := 
  gen_error false (Some ii) None (pp_vbox [::pp_box [:: pp_s "not able to compile the condition"; pp_e e];
                                             pp_s msg]).

Definition werror ii e msg := 
  gen_error false (Some ii) None (pp_vbox [::pp_box [:: pp_s "invalid pexpr for oprd"; pp_e e];
                                             pp_s msg]).

End E.

Definition fail ii (msg: string) :=
  asm_gen.E.error ii (pp_box [:: pp_s "store-label:"; pp_s msg]).

Section TOSTRING.

Context `{tS : ToString}.

(* move ? *)
Definition of_var_e ii (v: var_i) :=
  match of_var v with
  | Some r => ok r
  | None =>
    if vtype v == rtype then Error (E.invalid_name category ii v)
    else Error (E.invalid_ty category ii v)
  end.

Lemma of_var_eP {ii v r} :
  of_var_e ii v = ok r -> of_var v = Some r.
Proof.
  rewrite /of_var_e; case: of_var; last by case: eqP.
  by move=> _ [->].
Qed.

Lemma of_var_eI {ii v r} : of_var_e ii v = ok r -> to_var r = v.
Proof. by move => /of_var_eP; apply/of_varI. Qed.

Lemma inj_of_var_e {ii v1 v2 r}:
  of_var_e ii v1 = ok r -> of_var_e ii v2 = ok r -> v1 = v2 :> var.
Proof. by move => /of_var_eP h1 /of_var_eP; apply: inj_of_var. Qed.

End TOSTRING.

(* -------------------------------------------------------------------- *)

Section OF_TO.

Context {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond}.

Definition to_reg   : var -> option reg_t   := of_var.
Definition to_regx  : var -> option regx_t  := of_var.
Definition to_xreg  : var -> option xreg_t  := of_var.
Definition to_rflag : var -> option rflag_t := of_var.

Definition asm_typed_reg_of_var (x: var) : cexec asm_typed_reg :=
  match to_reg x with
  | Some r => ok (ARReg r)
  | None =>
  match to_regx x with
  | Some r => ok (ARegX r)
  | None => 
  match to_xreg x with
  | Some r => ok (AXReg r)
  | None =>
  match to_rflag x with
  | Some f => ok (ABReg f)
  | None =>  Error (E.gen_error true None None (pp_s "can not map variable to a register"))
  end end end end.

Definition var_of_asm_typed_reg (x : asm_typed_reg) : var :=
  match x with
  | ARReg r => to_var r
  | ARegX r => to_var r
  | AXReg r => to_var r
  | ABReg r => to_var r
  end.

Lemma asm_typed_reg_of_varI x r :
  asm_typed_reg_of_var x = ok r
  -> x = var_of_asm_typed_reg r:> var.
Proof.
  move=> h;apply/sym_eq; move:h;rewrite /asm_typed_reg_of_var.
  case heqr: (to_reg x) => [ ? | ].
  + by move=> [<-]; apply:of_varI.
  case heqrx: (to_regx x) => [ ? | ].
  + by move=> [<-]; apply: of_varI.
  case heqx: (to_xreg x) => [ ? | ].
  + by move=> [<-]; apply: of_varI.
  case heqf: (to_rflag x) => [ ? | //].
  by move=> [<-]; apply: of_varI.
Qed.

End OF_TO.

Section ASM_EXTRA.

Context `{asm_e : asm_extra} {call_conv: calling_convention}.


(* -------------------------------------------------------------------- *)
(* Compilation of pexprs *)
(* -------------------------------------------------------------------- *)

Record asm_gen_params :=
  {
    (* Assemble an expression into an architecture-specific condition. *)
    agp_assemble_cond : instr_info -> pexpr -> cexec cond_t;
  }.

Context
  (agparams : asm_gen_params).

Notation assemble_cond := (agp_assemble_cond agparams).

(* -------------------------------------------------------------------- *)
Definition scale_of_z' ii (z:pointer) : cexec nat :=
  match wunsigned z with
  | 1%Z => ok 0
  | 2%Z => ok 1
  | 4%Z => ok 2
  | 8%Z => ok 3
  | _ => Error (E.error ii (pp_s "invalid scale"))
  end.

Definition reg_of_ovar ii (x:option var_i) : cexec (option reg_t) :=
  match x with
  | Some x =>
    Let r := of_var_e ii x in
    ok (Some r)
  | None =>
    ok None
  end.

Definition assemble_lea ii lea :=
  Let base := reg_of_ovar ii lea.(lea_base) in
  Let offset := reg_of_ovar ii lea.(lea_offset) in
  Let scale := scale_of_z' ii lea.(lea_scale) in
  ok (Areg {|
      ad_disp := lea.(lea_disp);
      ad_base := base;
      ad_scale := scale;
      ad_offset := offset
    |}).

Let is_none {A: Type} (m: option A) : bool :=
      if m is None then true else false.

Definition addr_of_pexpr (rip:var) ii sz (e: pexpr) :=
  Let _ := assert (sz <= Uptr)%CMP
                  (E.error ii (pp_s "Bad type for address")) in
  match mk_lea sz e with
  | Some lea =>
     match lea.(lea_base) with
     | Some r =>
        if r.(v_var) == rip then
          Let _ := assert (is_none lea.(lea_offset))
                          (E.error ii (pp_box [::pp_s "Invalid global address :"; pp_e e])) in
          ok (Arip lea.(lea_disp))
        else assemble_lea ii lea
      | None =>
        assemble_lea ii lea
      end
  | None => Error (E.error ii (pp_box [::pp_s "not able to assemble address :"; pp_e e]))
  end.

Definition addr_of_xpexpr rip ii sz v e :=
  addr_of_pexpr rip ii sz (Papp2 (Oadd (Op_w sz)) (Plvar v) e).

Definition xreg_of_var ii (x: var_i) : cexec asm_arg :=
  if to_xreg x is Some r then ok (XReg r)
  else if to_reg x is Some r then ok (Reg r)
  else if to_regx x is Some r then ok (Regx r)
  else Error (E.verror false "Not a (x)register" ii x).

Definition assemble_word_load rip ii (sz:wsize) (e:pexpr) :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    let w := wrepr sz' z in
    let w1 := sign_extend sz w in
    let w2 := wrepr sz z in
    (* this check is not used (yet?) in the correctness proof *)
    Let _ := assert (w1 == w2)
                    (E.werror ii e "out of bound constant") in
    ok (Imm w)
  | Pvar x =>
    Let _ := assert (is_lvar x)
                    (E.internal_error ii "Global variables remain") in
    let x := x.(gv) in
    xreg_of_var ii x
  | Pload sz' v e' =>
    Let _ := assert (sz == sz')
                    (E.werror ii e "invalid Load size") in
    Let w := addr_of_xpexpr rip ii Uptr v e' in
    ok (Addr w)
  | _ => Error (E.werror ii e "invalid pexpr for word")
  end.

Definition assemble_word (k:addr_kind) rip ii (sz:wsize) (e:pexpr) :=
  match k with
  | AK_mem => assemble_word_load rip ii (sz:wsize) (e:pexpr)
  | AK_compute =>
    Let w := addr_of_pexpr rip ii sz e in
    ok (Addr w)
  end.

Definition arg_of_pexpr k rip ii (ty:stype) (e:pexpr) :=
  match ty with
  | sbool => Let c := assemble_cond ii e in ok (Condt c)
  | sword sz => assemble_word k rip ii sz e
  | sint  => Error (E.werror ii e "not able to assemble an expression of type int")
  | sarr _ => Error (E.werror ii e "not able to assemble an expression of type array _")
  end.

Definition pexpr_of_lval ii (lv:lval) : cexec pexpr :=
  match lv with
  | Lvar x          => ok (Plvar x)
  | Lmem s x e      => ok (Pload s x e)
  | Lnone _ _       => Error (E.internal_error ii "_ lval remains")
  | Laset _ _ _ _   => Error (E.internal_error ii "Laset lval remains")
  | Lasub _ _ _ _ _ => Error (E.internal_error ii "Lasub lval remains")
  end.

Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) :=
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Definition var_of_implicit (i:implicit_arg) :=
  match i with
  | IArflag f => to_var f
  | IAreg r   => to_var r
  end.

Definition compile_arg rip ii (ade: (arg_desc * stype) * pexpr) (m: nmap asm_arg) : cexec (nmap asm_arg) :=
  let ad := ade.1 in
  let e := ade.2 in
  match ad.1 with
  | ADImplicit i =>
    Let _ :=
      assert (eq_expr (Plvar (VarI (var_of_implicit i) dummy_var_info)) e)
             (E.internal_error ii "(compile_arg) bad implicit register") in
    ok m
  | ADExplicit k n o =>
    Let a := arg_of_pexpr k rip ii ad.2 e in
    Let _ :=
      assert (check_oreg o a)
             (E.internal_error ii "(compile_arg) bad forced register") in
    match nget m n with
    | None => ok (nset m n a)
    | Some a' =>
      if a == a' then ok m
      else Error (E.internal_error ii "(compile_arg) not compatible asm_arg")
    end
  end.

Definition compile_args rip ii adts (es:pexprs) (m: nmap asm_arg) :=
  foldM (compile_arg rip ii) m (zip adts es).

Definition compat_imm ty a' a := 
  (a == a') || match ty, a, a' with
             | sword sz, Imm sz1 w1, Imm sz2 w2 => sign_extend sz w1 == sign_extend sz w2
             | _, _, _ => false
             end.

Definition check_sopn_arg rip ii (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) dummy_var_info))
  | ADExplicit k n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr k rip ii adt.2 x is Ok a' then compat_imm adt.2 a a' && check_oreg o a
      else false
    | None => false
    end
  end.

Definition check_sopn_dest rip ii (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) dummy_var_info))
  | ADExplicit _ n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr AK_mem rip ii adt.2 x is Ok a' then (a == a') && check_oreg o a
      else false
    | None => false
    end
  end.

Definition error_imm ii :=
 E.error ii (pp_s "Invalid asm: cannot truncate the immediate to a 32 bits immediate, move it to a register first").

Definition assemble_asm_op_aux rip ii op (outx : lvals) (inx : pexprs) :=
  let id := instr_desc op in
  Let m := compile_args rip ii (zip id.(id_in) id.(id_tin)) inx (nempty _) in
  Let eoutx := mapM (pexpr_of_lval ii) outx in
  Let m := compile_args rip ii (zip id.(id_out) id.(id_tout)) eoutx m in
  match oseq.omap (nget m) (iota 0 id.(id_nargs)) with
  | None => Error (E.internal_error ii "compile_arg : assert false nget")
  | Some asm_args => ok asm_args
  end.

Definition check_sopn_args rip ii (loargs : seq asm_arg) (xs : seq pexpr) (adt : seq (arg_desc * stype)) :=
  all2 (check_sopn_arg rip ii loargs) xs adt.

Definition check_sopn_dests rip ii (loargs : seq asm_arg) (outx : seq lval) (adt : seq (arg_desc * stype)) :=
  match mapM (pexpr_of_lval ii) outx with
  | Ok eoutx => all2 (check_sopn_dest rip ii loargs) eoutx adt
  | _  => false
  end.

(* [check_arg_kind] but ignore constraints on immediate sizes *)
Definition check_arg_kind_no_imm (a:asm_arg) (cond: arg_kind) :=
  match a, cond with
  | Condt _, CAcond => true
  | Imm _ _, CAimm _ => true
  | Reg _ , CAreg => true
  | Regx _, CAregx => true
  | Addr _, CAmem _ => true
  | XReg _, CAxmm   => true
  | _, _ => false
  end.

(* Keep only the elements of [cond] that are compatible with [a].
   If the resulting list is empty, this means that no element of [cond] is
   compatible, and we return an error. This error is systematically caught by
   [filter_args_kinds_no_imm], thus we don't need a real error message, that's
   why we use [tt] as the error.
*)
Definition filter_arg_kinds_no_imm (a:asm_arg) (cond:arg_kinds) :=
  let cond' : arg_kinds := filter (check_arg_kind_no_imm a) cond in
  if cond' is [::] then Error tt else ok cond'.

(* We use [mapM2] so that we check that the two lists have equal lengths.
   But we don't need a real error message, thus we use [tt] as the error. *)
Definition filter_args_kinds_no_imm (args:asm_args) (cond:args_kinds) : option args_kinds :=
  match mapM2 tt (fun a c => filter_arg_kinds_no_imm a c) args cond with
  | Ok cond => Some cond
  | _ => None
  end.

Definition filter_i_args_kinds_no_imm (cond:i_args_kinds) (a:asm_args) : i_args_kinds :=
  pmap (filter_args_kinds_no_imm a) cond.

(* Enforce size constraints on immediates. *)
Definition enforce_imm_arg_kind (a:asm_arg) (cond: arg_kind) : option asm_arg :=
  match a, cond with
  | Condt _, CAcond => Some a
  | Imm sz w, CAimm sz' =>
    let w1 := zero_extend sz' w in
    let w2 := sign_extend sz w1 in
    (* this check is not used (yet?) in the correctness proof *)
    if w == w2 then Some (Imm w1) else None
  | Reg _, CAreg => Some a
  | Regx _, CAregx => Some a
  | Addr _, CAmem _ => Some a
  | XReg _, CAxmm   => Some a
  | _, _ => None
  end.

Definition enforce_imm_arg_kinds (a:asm_arg) (cond:arg_kinds) :=
  utils.find_map (enforce_imm_arg_kind a) cond.

(* We use [mapM2] so that we check that the two lists have equal lengths.
   But we don't need a real error message, thus we use [tt] as the error. *)
Definition enforce_imm_args_kinds (args:asm_args) (cond:args_kinds) : option asm_args :=
  match mapM2 tt (fun a c => o2r tt (enforce_imm_arg_kinds a c)) args cond with
  | Ok args => Some args
  | _ => None
  end.

Definition enforce_imm_i_args_kinds (cond:i_args_kinds) (a:asm_args) :=
  utils.find_map (enforce_imm_args_kinds a) cond.

Definition pp_arg_kind c :=
  match c with
  | CAmem b => pp_nobox [:: pp_s "mem (glob "; pp_s (if b then "" else "not ")%string; pp_s "allowed)"]
  | CAimm ws => pp_nobox [:: pp_s "imm "; pp_s (string_of_wsize ws)]
  | CAcond => pp_s "cond"
  | CAreg => pp_s "reg"
  | CAregx => pp_s "regx"
  | CAxmm => pp_s "xreg"
  end.

Fixpoint pp_list {A} sep (pp : A -> pp_error) xs : seq pp_error :=
  match xs with
  | [::] => [::]
  | [:: x] => [:: pp x]
  | x :: xs => pp x :: sep :: (pp_list sep pp xs)
  end.

Definition pp_arg_kinds cond :=
  pp_box [:: pp_nobox (pp_s "[" :: pp_list (pp_nobox [:: pp_s ";"; PPEbreak]) pp_arg_kind cond ++ [:: pp_s "]"])].

Definition pp_args_kinds cond :=
  pp_box [:: pp_nobox (pp_s "[" :: pp_list (pp_nobox [:: pp_s ";"; PPEbreak]) pp_arg_kinds cond ++ [:: pp_s "]"])].

Definition pp_i_args_kinds cond :=
  pp_vbox [:: pp_nobox (pp_list PPEbreak pp_args_kinds cond)].

Definition assemble_asm_op rip ii op (outx : lvals) (inx : pexprs) := 
  let id := instr_desc op in
  Let asm_args := assemble_asm_op_aux rip ii op outx inx in
  let s := id.(id_str_jas) tt in
  let args_kinds := filter_i_args_kinds_no_imm id.(id_args_kinds) asm_args in
  Let _ := assert (args_kinds != [::])
                  (E.error ii (pp_nobox [::
                    pp_box [:: pp_s "instruction"; pp_s s; pp_s "is given incompatible args."]; PPEbreak;
                    pp_vbox [::
                      pp_s "Allowed args are:";
                      pp_nobox [:: pp_s "  "; pp_i_args_kinds id.(id_args_kinds)]]])) in
  Let asm_args :=
    if enforce_imm_i_args_kinds args_kinds asm_args is Some asm_args then
      ok asm_args
    else
      Error (E.error ii (pp_nobox [::
        pp_box [:: pp_s "instruction"; pp_s s; pp_s "is given at least one too large immediate as an argument."]; PPEbreak;
        pp_vbox [::
        pp_s "Allowed args compatible with the input (except on immediate sizes) are:";
        pp_nobox [::pp_s "  "; pp_vbox [::
        pp_i_args_kinds args_kinds]];
        pp_s "All allowed args (regardless of the input) are:";
        pp_nobox [:: pp_s "  "; pp_vbox [::
        pp_i_args_kinds id.(id_args_kinds)]]]]))
  in
  Let _ := assert (check_sopn_args rip ii asm_args inx (zip id.(id_in) id.(id_tin)) &&
                     check_sopn_dests rip ii asm_args outx (zip id.(id_out) id.(id_tout)))
                  (E.internal_error ii "assemble_asm_opn: cannot check") in
  ok (op.2, asm_args).

Definition assemble_sopn rip ii (op:sopn) (outx : lvals) (inx : pexprs) :=
  match op with
  | Ocopy _ _
  | Onop
  | Omulu     _ 
  | Oaddcarry _ 
  | Osubcarry _ =>
    Error (E.internal_error ii "assemble_sopn : invalid op")
  (* Low level x86 operations *)
  | Oasm (BaseOp op) =>
    assemble_asm_op rip ii op outx inx
  | Oasm (ExtOp op) =>
    Let: (op, outx, inx) := to_asm ii op outx inx in
    assemble_asm_op rip ii op outx inx
  end.

(* -------------------------------------------------------------------- *)

Definition assemble_i (rip : var) (i : linstr) : cexec asm_i :=
  let '{| li_ii := ii; li_i := ir; |} := i in
  match ir with
  | Lopn ds op es =>
      Let  ao := assemble_sopn rip ii op ds es in
      ok (AsmOp ao.1 ao.2)

  | Lalign =>
      ok ALIGN

  | Llabel lbl =>
      ok (LABEL lbl)

  | Lgoto lbl =>
      ok (JMP lbl)

  | Ligoto e =>
      Let _ := assert (is_none (is_app1 e)) (E.werror ii e "Ligoto/JMPI") in
      Let arg := assemble_word AK_mem rip ii Uptr e in
      ok (JMPI arg)

  | LstoreLabel x lbl =>
      Let dst := if of_var x is Some r then ok r else Error (fail ii "bad var") in
      ok (STORELABEL dst lbl)

  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ok (Jcc l cond)

  | Lsyscall o =>
      ok (SysCall o)
  end.

(* -------------------------------------------------------------------- *)
(*TODO: use in whatever characterization using an lprog there is.*)
Definition assemble_c rip (lc: lcmd) : cexec (seq asm_i) :=
  mapM (assemble_i rip) lc.

(* -------------------------------------------------------------------- *)

Definition is_typed_reg x := 
   (vtype x != sbool) &&
   is_ok (asm_typed_reg_of_var x).

Definition typed_reg_of_vari xi :=
  let '{| v_var := x; |} := xi in asm_typed_reg_of_var x.

Definition assemble_fd (rip rsp : var) (fd : lfundef) :=
  Let fd' := assemble_c rip (lfd_body fd) in
  Let _ := assert
    (rsp \notin map v_var fd.(lfd_arg))
    (E.gen_error true None None (pp_s "Stack pointer is an argument")) in
  Let _ := assert
    (all is_typed_reg fd.(lfd_callee_saved))
    (E.gen_error true None None (pp_s "Saved variable is not a register")) in 
  Let arg := mapM typed_reg_of_vari fd.(lfd_arg) in
  Let res := mapM typed_reg_of_vari fd.(lfd_res) in
  let fd := 
    {| asm_fd_align := lfd_align fd
     ; asm_fd_arg := arg
     ; asm_fd_body := fd'
     ; asm_fd_res := res
     ; asm_fd_export := lfd_export fd
     ; asm_fd_total_stack := lfd_total_stack fd
    |} in

  Let _ := assert (check_call_conv fd) 
                  (E.gen_error true None None (pp_s "export function does not respect the calling convention")) in
  ok fd.

(* -------------------------------------------------------------------- *)

(* [map_cfprog_gen] specialized to functions of type [lfundef] *)
Notation map_cfprog_linear := (map_cfprog_gen lfd_info).

Definition assemble_prog (p : lprog) : cexec asm_prog :=
  let rip := mk_ptr (lp_rip p) in
  let rsp := mk_ptr (lp_rsp p) in
  Let _ :=
    assert
      ((to_reg  rip == None :> option_eqType ceqT_eqType) && 
       (to_regx rip == None :> option_eqType ceqT_eqType))  
      (E.gen_error true None None (pp_s "Invalid RIP"))
  in
  Let _ :=
    assert
      (of_string (lp_rsp p) == Some ad_rsp :> option_eqType ceqT_eqType)
      (E.gen_error true None None (pp_s "Invalid RSP"))
  in
  Let fds :=
    map_cfprog_linear (assemble_fd rip rsp) (lp_funcs p)
  in
  ok {| asm_globs := lp_globs p; asm_funcs := fds; |}.

End ASM_EXTRA.

Section OVM_I.

Context {reg regx xreg rflag cond} {ad : arch_decl reg regx xreg rflag cond} {call_conv: calling_convention}.

Definition vflags := sv_of_list to_var rflags.

Lemma vflagsP x : Sv.In x vflags -> vtype x = sbool.
Proof. by move=> /sv_of_listP /in_map [? _ ->]. Qed.

Definition all_vars :=
    Sv.union (sv_of_list to_var registers)
   (Sv.union (sv_of_list to_var registerxs)
   (Sv.union (sv_of_list to_var xregisters)
             vflags)).

#[global] Instance ovm_i : one_varmap.one_varmap_info := {
  syscall_sig  :=
    fun o =>
      let sig := syscall_sig_s o in
      {| scs_vin  := map to_var (take (size sig.(scs_tin)) call_reg_args);
         scs_vout := map to_var (take (size sig.(scs_tout)) call_reg_ret) |};
  all_vars     := all_vars; 
  callee_saved := sv_of_list var_of_asm_typed_reg callee_saved;
  vflags       := vflags;
  vflagsP      := vflagsP;
}.

End OVM_I.

Notation map_cfprog_linear := (map_cfprog_gen lfd_info).
