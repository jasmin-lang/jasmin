From Coq Require Import Utf8 Relation_Operators.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import compiler_util expr values linear asm_gen arch_extra.
Require Import sem_one_varmap. (* needed to have syscall_kill *)
Require Import x86_decl x86_instr_decl x86_extra x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import compiler_util.

(* TODO: half of this file is not x86-dependent and could become architecture-generic *)

(* -------------------------------------------------------------------- *)

Definition fail ii (msg: string) :=
  asm_gen.E.error ii (pp_box [:: pp_s "store-label:"; pp_s msg]).

Definition not_condt (c:condt) := 
  match c with
  | O_ct  => NO_ct
  | NO_ct => O_ct
  | B_ct  => NB_ct 
  | NB_ct => B_ct
  | E_ct  => NE_ct 
  | NE_ct => E_ct 
  | BE_ct => NBE_ct 
  | NBE_ct => BE_ct 
  | S_ct   => NS_ct 
  | NS_ct  => S_ct 
  | P_ct   => NP_ct 
  | NP_ct  => P_ct 
  | L_ct   => NL_ct 
  | NL_ct  => L_ct 
  | LE_ct  => NLE_ct 
  | NLE_ct => LE_ct
  end.

Definition or_condt ii e c1 c2 : cexec condt := 
  match c1, c2 with
  | L_ct, E_ct | E_ct, L_ct => ok LE_ct
  | B_ct, E_ct | E_ct, B_ct => ok BE_ct 
  | _, _ => Error (E.berror ii e "Invalid condition (OR)")
  end.

Definition and_condt ii e c1 c2 := 
  match c1, c2 with
  | NB_ct, NE_ct | NE_ct, NB_ct => ok NBE_ct
  | NE_ct, NL_ct | NL_ct, NE_ct => ok NLE_ct 
  | _, _ => Error (E.berror ii e "Invalid condition (AND)")
  end.

Fixpoint assemble_cond_r ii (e: pexpr) : cexec condt :=
  match e with
  | Pvar v =>
    Let r := of_var_e ii v.(gv) in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => Error (E.berror ii e "Cannot branch on DF")
    end
  | Papp1 Onot e => 
    Let c := assemble_cond_r ii e in
    ok (not_condt c)

  | Papp2 Oor e1 e2 =>
    Let c1 := assemble_cond_r ii e1 in
    Let c2 := assemble_cond_r ii e2 in
    or_condt ii e c1 c2
  
  | Papp2 Oand e1 e2 =>
    Let c1 := assemble_cond_r ii e1 in
    Let c2 := assemble_cond_r ii e2 in
    and_condt ii e c1 c2
    
  | Papp2 Obeq (Pvar x1) (Pvar x2) =>
    Let r1 := of_var_e ii x1.(gv) in
    Let r2 := of_var_e ii x2.(gv) in
    if (r1 == SF) && (r2 == OF) || (r1 == OF) && (r2 == SF) then ok NL_ct
    else Error (E.berror ii e "Invalid condition (NL)")
  
  (* We keep this by compatibility but it will be nice to remove it *)
  | Pif _ (Pvar v1) (Papp1 Onot (Pvar vn2)) (Pvar v2) =>
    Let r1 := of_var_e ii v1.(gv) in
    Let rn2 := of_var_e ii vn2.(gv) in
    Let r2 := of_var_e ii v2.(gv) in
    if [&& r1 == SF, rn2 == OF & r2 == OF] ||
       [&& r1 == OF, rn2 == SF & r2 == SF] then
      ok L_ct
    else Error (E.berror ii e "Invalid condition (L)")

  | Pif _ (Pvar v1) (Pvar v2) (Papp1 Onot (Pvar vn2)) =>
    Let r1 := of_var_e ii v1.(gv) in
    Let r2 := of_var_e ii v2.(gv) in
    Let rn2 := of_var_e ii vn2.(gv) in
    if [&& r1 == SF, rn2 == OF & r2 == OF] ||
       [&& r1 == OF, rn2 == SF & r2 == SF] then
      ok NL_ct
    else  Error (E.berror ii e "Invalid condition (NL)")
  
  | _ => Error (E.berror ii e "don't known how to compile the condition")

  end.

Definition assemble_cond ii (e: pexpr) : cexec condt :=
  assemble_cond_r ii e.

Definition assemble_i (rip:var) (i: linstr) : cexec asm_i :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
  | Lopn ds op es => 
    Let oa := assemble_sopn assemble_cond rip ii op ds es in
    ok (AsmOp oa.1 oa.2)

  | Lsyscall o => ok (SysCall o)

  | Lalign  => ok ALIGN

  | Llabel lbl =>  ok (LABEL lbl)

  | Lgoto lbl => ok (JMP lbl)

  | Ligoto e =>
    Let _ := assert (if e is Papp1 _ _ then false else true) (E.werror ii e "Ligoto/JMPI") in
    Let arg := assemble_word AK_mem rip ii Uptr e in
    ok (JMPI arg)

  | LstoreLabel x lbl =>
   
    Let dst := match x with
    | Lvar x => if of_var x is Some r then ok r else Error (fail ii "bad var")
    | Lmem _ _ _ => Error (fail ii "set mem")
    | Laset _ _ _ _ => Error (fail ii "set array")
    | Lasub _ _ _ _ _ => Error (fail ii "sub array")
    | Lnone _ _ => Error (fail ii "none")
    end%string in
    ok (STORELABEL dst lbl)
  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ok (Jcc l cond)
  end.

(* -------------------------------------------------------------------- *)
(*TODO: use in whatever characterization using an lprog there is.*)
Definition assemble_c rip (lc: lcmd) : cexec (seq asm_i) :=
  mapM (assemble_i rip) lc.

(* -------------------------------------------------------------------- *)
Definition asm_typed_reg_of_var (x: var) : cexec asm_typed_reg :=
  let: {| vtype := ty ; vname := n |} := x in
  match ty with
  | sbool => if of_string n is Some r then ok (ABReg r) else Error (E.gen_error true None None (pp_s "6qJYxxWakSyc%"))
  | sint => Error (E.gen_error true None None (pp_s "vBuu8Nv7AFRC"))
  | sarr _ => Error (E.gen_error true None None (pp_s "4WLdO8K4viE3"))
  | sword sz =>
      match sz with
      | U64 => if of_string n is Some r then ok (ARReg r) else Error (E.gen_error true None None (pp_s "R+zT50uyf3fF"))
      | U256=> if of_string n is Some r then ok (AXReg r) else Error (E.gen_error true None None (pp_s "Dh9l31MJeafV"))
      | _ => Error (E.gen_error true None None (pp_s "+y2SvS1t6pzB"))
      end
  end.

Definition var_of_asm_typed_reg (x : asm_typed_reg) : var :=
  match x with
  | ARReg r => to_var r
  | AXReg r => to_var r
  | ABReg r => to_var r
  end.

Lemma asm_typed_reg_of_varI x r :
  asm_typed_reg_of_var x = ok r →
  x = var_of_asm_typed_reg r :> var.
Proof.
  rewrite /asm_typed_reg_of_var.
  case: x => xt x /=.
  case: xt => [ | // | // | [] // ].
  all: case e: of_string => [ y | // ] /ok_inj <-.
  all: by rewrite -(of_stringI e).
Qed.

(* -------------------------------------------------------------------- *)
Definition assemble_fd (sp:register) rip (fd: lfundef) :=
  Let fd' := assemble_c rip (lfd_body fd) in
  Let _ := assert
             (~~ (to_var sp \in map v_var fd.(lfd_arg)))
             ( E.gen_error true None None (pp_s "Stack pointer is an argument")) in
  Let _ := assert
             (all (λ x, if asm_typed_reg_of_var x is Ok (ARReg _) then true else false) (lfd_callee_saved fd))
             (E.gen_error true None None (pp_s "Saved variable is not a register")) in
  Let arg := mapM (λ x : var_i, asm_typed_reg_of_var x) fd.(lfd_arg) in
  Let res := mapM (λ x : var_i, asm_typed_reg_of_var x) fd.(lfd_res) in
  ok {|
      asm_fd_align := lfd_align fd
    ; asm_fd_arg := arg
    ; asm_fd_body := fd'
    ; asm_fd_res := res
    ; asm_fd_export := lfd_export fd
    ; asm_fd_total_stack := lfd_total_stack fd
    |}.

(* -------------------------------------------------------------------- *)

Definition mk_rip name := {| vtype := sword Uptr; vname := name |}.

(* [map_cfprog_gen] specialized to functions of type [lfundef] *)
Notation map_cfprog_linear := (map_cfprog_gen lfd_info).

Definition assemble_prog (p: lprog) : cexec asm_prog :=
  let rip := mk_rip p.(lp_rip) in
  Let _ := assert (to_reg rip == None)
                  ( E.gen_error true None None (pp_s "Invalid RIP")) in
  Let _ := assert (of_string p.(lp_rsp) == Some RSP)
                  ( E.gen_error true None None (pp_s "Invalid RSP")) in
  Let fds := map_cfprog_linear (assemble_fd RSP rip) p.(lp_funcs) in
  ok {| asm_globs := p.(lp_globs); asm_funcs := fds |}.

Definition get_typed_reg_value (st: x86_mem) (r: asm_typed_reg) : exec value :=
  match r with
  | ARReg r => ok (Vword (asm_reg st r))
  | AXReg r => ok (Vword (asm_xreg st r))
  | ABReg r => if asm_flag st r is Def b then ok (Vbool b) else undef_error
  end.

Definition get_typed_reg_values st rs : exec values :=
  mapM (get_typed_reg_value st) rs.
