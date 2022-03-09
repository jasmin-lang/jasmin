From mathcomp Require Import all_ssreflect all_algebra.
Require Import oseq compiler_util expr low_memory lea arch_decl arch_extra.
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

Definition berror ii e msg := 
  gen_error false (Some ii) None (pp_vbox [::pp_box [:: pp_s "not able to compile the condition"; pp_e e];
                                             pp_s msg]).

Definition werror ii e msg := 
  gen_error false (Some ii) None (pp_vbox [::pp_box [:: pp_s "invalid pexpr for oprd"; pp_e e];
                                             pp_s msg]).

End E.

Section TOSTRING.

Context `{tS : ToString}.

(* move ? *)
Definition of_var_e ii (v: var_i) :=
  match of_var v with
  | Some r => ok r
  | None =>
    if vtype v == rtype then Error (E.invalid_ty category ii v)
    else Error (E.invalid_name category ii v)
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

Section ASM_EXTRA.

Context `{asm_e : asm_extra}.

Definition to_reg   : var -> option reg_t   := of_var.
Definition to_regx  : var -> option regx_t  := of_var.
Definition to_xreg  : var -> option xreg_t  := of_var.
Definition to_rflag : var -> option rflag_t := of_var.

(* -------------------------------------------------------------------- *)
Variant compiled_variable :=
| LReg   of reg_t
| LXReg  of xreg_t
| LRFlag of rflag_t
.

Definition compiled_variable_beq cv1 cv2 :=
  match cv1, cv2 with
  | LReg   r1, LReg   r2 => r1 == r2 ::>
  | LXReg  r1, LXReg  r2 => r1 == r2 ::>
  | LRFlag f1, LRFlag f2 => f1 == f2 ::>
  | _, _ => false
  end.

Lemma compiled_variable_eq_axiom : Equality.axiom compiled_variable_beq.
Proof.
  move=> [r1 | x1 | f1] [r2 | x2 | f2] /=;
    (by constructor || by apply:(iffP idP) => [ /eqP -> | [->] ]).
Qed.

Definition compiled_variable_eqMixin := Equality.Mixin compiled_variable_eq_axiom.
Canonical  compiled_variable_eqType  := Eval hnf in EqType compiled_variable compiled_variable_eqMixin.

Definition compile_var (v: var) : option compiled_variable :=
  match to_reg v with
  | Some r => Some (LReg r)
  | None =>
  match to_xreg v with
  | Some r => Some (LXReg r)
  | None =>
  match to_rflag v with
  | Some f => Some (LRFlag f)
  | None => None
  end end end.

Lemma compile_varI x cv :
  compile_var x = Some cv →
  match cv with
  | LReg r   => to_var r = x
  | LXReg r  => to_var r = x
  | LRFlag f => to_var f = x
  end.
Proof.
  rewrite /compile_var.
  case heqr: (to_reg x) => [ r | ].
  + by move=> [<-]; apply: of_varI.
  case heqx: (to_xreg x) => [ r | ].
  + by move=> [<-]; apply: of_varI.
  case heqf: (to_rflag x) => [ r | //].
  by move=> [<-]; apply: of_varI.
Qed.

(* -------------------------------------------------------------------- *)
(* Compilation of pexprs *)
(* -------------------------------------------------------------------- *)

Context (assemble_cond : instr_info -> pexpr -> cexec cond_t).

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

Definition addr_of_pexpr (rip:var) ii sz (e: pexpr) :=
  Let _ := assert (sz <= Uptr)%CMP
                  (E.error ii (pp_s "Bad type for address")) in
  match mk_lea sz e with
  | Some lea =>
     match lea.(lea_base) with
     | Some r =>
        if r.(v_var) == rip then
          Let _ := assert (lea.(lea_offset) == None)
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
      assert (eq_expr (Plvar (VarI (var_of_implicit i) xH)) e)
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
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
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
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
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

End ASM_EXTRA.
