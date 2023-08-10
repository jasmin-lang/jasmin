(* * Syntax of the linear language *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr fexpr label sopn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_OP.

Context `{asmop:asmOp}.

(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Variant linstr_r :=
  | Lopn   : lexprs -> sopn -> rexprs -> linstr_r
  | Lsyscall : syscall_t -> linstr_r
  | Lcall    : option var_i -> remote_label -> linstr_r 
     (* Lcall ra lbl: 
        if ra = Some r the return adress is stored in r else on top of the stack *)
  | Lret     : linstr_r
  | Lalign : linstr_r
  | Llabel : label_kind -> label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : rexpr -> linstr_r (* Absolute indirect jump *)
  | LstoreLabel : var -> label -> linstr_r
  | Lcond  : fexpr -> label -> linstr_r
.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.

Definition is_label (lbl: label) (i: linstr) : bool :=
  match i.(li_i) with
  | Llabel _ lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (c : seq linstr) :=
  let idx := seq.find (is_label lbl) c in
  if idx < size c then ok idx else type_error.

Record lfundef := LFundef {
 lfd_info : fun_info;
 lfd_align : wsize;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_export: bool;
 lfd_callee_saved: seq var; (* A list of variables that must be initialized before calling this function *)
 lfd_total_stack: Z; (* total amount of stack memory needed by this function (and all functions called by this one *)
}.

Definition with_lbody (lfd : lfundef) (lbody : lcmd) : lfundef :=
  {|
    lfd_info := lfd_info lfd;
    lfd_align := lfd_align lfd;
    lfd_tyin := lfd_tyin lfd;
    lfd_arg := lfd_arg lfd;
    lfd_body := lbody;
    lfd_tyout := lfd_tyout lfd;
    lfd_res := lfd_res lfd;
    lfd_export := lfd_export lfd;
    lfd_callee_saved := lfd_callee_saved lfd;
    lfd_total_stack := lfd_total_stack lfd;
  |}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Record lprog :=
 {  lp_rip   : Ident.ident;
    lp_rsp : Ident.ident;
    lp_globs : seq u8;
    lp_funcs : seq (funname * lfundef) }.

Definition with_lfds (lp : lprog) (lfds : seq (funname * lfundef)) : lprog :=
  {|
    lp_rip := lp_rip lp;
    lp_rsp := lp_rsp lp;
    lp_globs := lp_globs lp;
    lp_funcs := lfds;
  |}.

End ASM_OP.

Notation fopn_args := (seq lexpr * sopn * seq rexpr)%type (only parsing).

Definition lir_of_fopn_args
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (args : fopn_args)
  : linstr_r :=
  Lopn args.1.1 args.1.2 args.2.

Definition li_of_fopn_args
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (ii : instr_info)
  (args : fopn_args) :
  linstr :=
  MkLI ii (lir_of_fopn_args args).
