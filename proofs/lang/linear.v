(* * Syntax of the linear language *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr label sopn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_OP.

Context `{asmop:asmOp}.

(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Variant linstr_r :=
  | Lopn   : lvals -> sopn -> pexprs -> linstr_r
  | Lsyscall : syscall_t -> linstr_r
  | Lcall    : remote_label -> linstr_r
  | Lret     : linstr_r
  | Lalign : linstr_r
  | Llabel : label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : pexpr -> linstr_r (* Absolute indirect jump *)
  | LstoreLabel : var -> label -> linstr_r
  | Lcond  : pexpr -> label -> linstr_r
.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.

Definition is_label (lbl: label) (i:linstr) : bool :=
  match i.(li_i) with
  | Llabel lbl' => lbl == lbl'
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
 (* This is [lfd_total_stack] without padding, rounded to the next alignment
    multiple if the function is export and we need to clean the stack. *)
  lfd_used_stack : Z;
}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Definition map_lfundef (f : lcmd -> lcmd) (lfd : lfundef) : lfundef :=
  {|
    lfd_info := lfd_info lfd;
    lfd_align := lfd_align lfd;
    lfd_tyin := lfd_tyin lfd;
    lfd_arg := lfd_arg lfd;
    lfd_body := f (lfd_body lfd);
    lfd_tyout := lfd_tyout lfd;
    lfd_res := lfd_res lfd;
    lfd_export := lfd_export lfd;
    lfd_callee_saved := lfd_callee_saved lfd;
    lfd_total_stack := lfd_total_stack lfd;
    lfd_used_stack := lfd_used_stack lfd;
  |}.


(* -------------------------------------------------------------------- *)

Record lprog :=
  {
    lp_rip : Ident.ident;
    lp_rsp : Ident.ident;
    lp_globs : seq u8;
    lp_funcs : seq (funname * lfundef);
  }.

Definition map_lprog_name
  (f : funname -> lfundef -> lfundef) (lp : lprog) : lprog :=
  {|
    lp_rip := lp_rip lp;
    lp_rsp := lp_rsp lp;
    lp_globs := lp_globs lp;
    lp_funcs := map (fun '(fn, fd) => (fn, f fn fd)) (lp_funcs lp);
  |}.

Definition map_lprog (f : lfundef -> lfundef) (lp : lprog) : lprog :=
  map_lprog_name (fun _ => f) lp.

Fixpoint max_map
  {A B : Type} `{Cmp B} (f : A -> option B) xs acc : option B :=
  match xs with
  | [::] => acc
  | x :: xs' =>
      let acc' :=
        if f x is Some y
        then Some (if acc is Some z then max y z else y)
        else acc
      in
      max_map f xs' acc'
  end.

Definition max_lcmd_lbl (c : lcmd) : option label :=
  let f '(MkLI _ i) :=
    if i is Llabel lbl
    then Some lbl
    else None
  in
  max_map f c None.

Definition max_lfd_lbl (lfd : lfundef) : option label :=
  max_lcmd_lbl (lfd_body lfd).

Definition max_lprog_lbl (p : lprog) : option label :=
  max_map (fun '(_, fd) => max_lfd_lbl fd) (lp_funcs p) None.

Definition next_lbl lbl := (lbl + 1)%positive.

Definition next_lprog_lbl (p : lprog) : label :=
  if max_lprog_lbl p is Some lbl
  then next_lbl lbl
  else xH.

End ASM_OP.
