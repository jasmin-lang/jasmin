Require Import x86_sem linear_sem.
Import Utf8 Relation_Operators.
Import all_ssreflect all_algebra.
Require Import compiler_util expr psem x86_sem linear x86_variables asmgen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import compiler_util.
(* -------------------------------------------------------------------- *)

Definition fail ii (msg: string) :=
  E.error ii (pp_box [:: pp_s "store-label:"; pp_s msg]).

Definition assemble_i rip (i: linstr) : cexec asm_i :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
  | Lopn ds op es => 
    Let oa := assemble_sopn rip ii op ds es in
    ok (AsmOp oa.1 oa.2)

  | Lalign  => ok ALIGN

  | Llabel lbl =>  ok (LABEL lbl)

  | Lgoto lbl => ok (JMP lbl)

  | Ligoto e =>
    Let _ := assert (if e is Papp1 _ _ then false else true) (E.werror ii e "Ligoto/JMPI") in
    Let arg := assemble_word AK_mem rip ii Uptr e in
    ok (JMPI arg)

  | LstoreLabel x lbl =>
   
    Let dst := match x with
    | Lvar x => if register_of_var x is Some r then ok r else Error (fail ii "bad var")
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

Definition assemble_fd sp rip (fd: lfundef) :=
  Let fd' := assemble_c rip (lfd_body fd) in
  Let _ := assert
             (~~ (var_of_register sp \in map v_var fd.(lfd_arg)))
             ( E.gen_error true None None (pp_s "Stack pointer is an argument")) in
  ok (XFundef (lfd_align fd) [::] fd' [::] (lfd_export fd)).
  (* FIXME: I put [::] so that it compiles but this must be changed with real values *)

(* -------------------------------------------------------------------- *)

Definition mk_rip name := {| vtype := sword Uptr; vname := name |}.

(* [map_cfprog_gen] specialized to functions of type [lfundef] *)
Notation map_cfprog_linear := (map_cfprog_gen lfd_info).

Definition assemble_prog (p: lprog) : cexec asm_prog :=
  let rip := mk_rip p.(lp_rip) in
  Let _ := assert (register_of_var rip == None)
                  ( E.gen_error true None None (pp_s "Invalid RIP")) in
  Let _ := assert (reg_of_string p.(lp_rsp) == Some RSP)
                  ( E.gen_error true None None (pp_s "Invalid RSP")) in
  Let fds := map_cfprog_linear (assemble_fd RSP rip) p.(lp_funcs) in
  ok {| asm_globs := p.(lp_globs); asm_funcs := fds |}.

Definition get_arg_value (st: x86_mem) (a: asm_arg) : value :=
  match a with
  | Reg r => Vword (asm_reg st r)
  | XReg r => Vword (asm_xreg st r)
  | Condt _ | Imm _ _ | Addr _ => Vundef sword64 (refl_equal _)
  end.

Definition get_arg_values st rs : values :=
  map (get_arg_value st) rs.
